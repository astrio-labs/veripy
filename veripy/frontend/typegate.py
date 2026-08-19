"""Type gate: run basedpyright over files and surface its diagnostics.

ARCHITECTURE §3's conformance front-end is two passes: **basedpyright strict**
(solves dynamic *typing*; version-pinned and trusted, assumption A7) followed
by the AST allowlist pass (solves dynamic *semantics*). This module wires the
first pass into `veripy check`: a file's functions are not clean unless
basedpyright reports zero errors for that file.

Project settings come from the governing pyright configuration: files are
grouped by their nearest `pyrightconfig.json` (or `pyproject.toml` with a
[tool.pyright]/[tool.basedpyright] table) and each group is checked in its own
project context, so one command spanning several projects applies each
project's settings — **except weakness**. A config whose `typeCheckingMode`
is weaker than "strict" cannot lower the gate: those files fail with a
`veripy-strict-required` diagnostic instead of being checked meaninglessly.
An unset mode is acceptable because basedpyright's default ("recommended") is
stricter than "strict". The same fail-closed rule applies per path:
`executionEnvironments` entries are honored for *structural* settings
(root/pythonVersion/pythonPlatform/extraPaths), but an environment that
overrides diagnostic settings for a gated file fails that file — path-varying
diagnostics defeat the claim "this file was checked strictly". Top-level
per-rule overrides are not policed: they are uniform and visible in one
place, i.e. the project's own auditable choice. Config inheritance via
`extends` is resolved before any of these checks (child keys override base
keys, pyright's semantics); an unreadable link or a cycle in the chain fails
closed. executionEnvironment roots are checked under both the declaring
config's directory and the governing config's directory — coverage under
either flags the file, so the over-approximation fails closed regardless of
which resolution the checker applies. If basedpyright cannot
run, the gate reports unavailable and `veripy check` FAILS — skipping type
analysis is only possible via the explicit `--no-types` opt-out.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path


@dataclass(frozen=True)
class TypeDiagnostic:
    file: str
    line: int  # 1-based
    severity: str
    message: str
    rule: str | None


@dataclass
class TypeGateResult:
    available: bool
    version: str | None = None
    diagnostics: list[TypeDiagnostic] = field(default_factory=list)
    error: str | None = None

    @property
    def errors(self) -> list[TypeDiagnostic]:
        return [d for d in self.diagnostics if d.severity == "error"]

    @property
    def warnings(self) -> list[TypeDiagnostic]:
        return [d for d in self.diagnostics if d.severity == "warning"]


def find_basedpyright() -> str | None:
    exe = shutil.which("basedpyright")
    if exe:
        return exe
    candidate = Path(sys.executable).parent / "basedpyright"
    return str(candidate) if candidate.exists() else None


def _has_pyright_table(pyproject: Path) -> bool:
    try:
        text = pyproject.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    return "[tool.pyright]" in text or "[tool.basedpyright]" in text


def _governing_config_dir(path: Path) -> Path | None:
    """Nearest ancestor directory carrying a pyright configuration."""
    for parent in [path.parent, *path.parent.parents]:
        if (parent / "pyrightconfig.json").exists():
            return parent
        if _has_pyright_table(parent / "pyproject.toml"):
            return parent
    return None


# Modes at least as strong as "strict" ("recommended"/"all" are basedpyright's
# stricter tiers). Anything else cannot satisfy the gate.
_STRICT_OK_MODES = frozenset({"strict", "recommended", "all"})

# executionEnvironments keys that configure the environment rather than
# weaken diagnostics; anything else in an environment entry fails the gate
# for files under that root.
_ENV_STRUCTURAL_KEYS = frozenset({"root", "pythonVersion", "pythonPlatform", "extraPaths"})


def _strip_jsonc(text: str) -> str:
    """Reduce pyright's JSONC (// and /* */ comments, trailing commas) to
    strict JSON. String-aware; two passes so a comment sitting between a
    trailing comma and its closing bracket is handled."""
    out: list[str] = []
    i, n = 0, len(text)
    in_str = False
    while i < n:
        c = text[i]
        if in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            i += 2
            while i + 1 < n and not (text[i] == "*" and text[i + 1] == "/"):
                i += 1
            i += 2
            continue
        out.append(c)
        i += 1

    # Second pass: drop trailing commas (comments are already gone).
    text2 = "".join(out)
    out2: list[str] = []
    i, n = 0, len(text2)
    in_str = False
    while i < n:
        c = text2[i]
        if in_str:
            out2.append(c)
            if c == "\\" and i + 1 < n:
                out2.append(text2[i + 1])
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            out2.append(c)
            i += 1
            continue
        if c == ",":
            j = i + 1
            while j < n and text2[j] in " \t\r\n":
                j += 1
            if j < n and text2[j] in "}]":
                i += 1
                continue
        out2.append(c)
        i += 1
    return "".join(out2)


def _read_config_json(path: Path) -> dict | None:
    """Parse one pyrightconfig-style JSONC file; None = unreadable."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
        data = json.loads(_strip_jsonc(text))
    except (OSError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def _resolve_extends(path: Path, seen: frozenset[Path]) -> dict | None:
    """Effective config with the `extends` chain resolved — child keys
    override base keys at top-level granularity, matching pyright. None on
    any unreadable link or a cycle (fail closed)."""
    real = path.resolve()
    if real in seen:
        return None
    data = _read_config_json(real)
    if data is None:
        return None
    _tag_env_declaring_dir(data, real.parent)
    extends = data.get("extends")
    if isinstance(extends, str):
        base = _resolve_extends(real.parent / extends, seen | {real})
        if base is None:
            return None
        return {**base, **{k: v for k, v in data.items() if k != "extends"}}
    return data


_DECLARING_DIR_KEY = "_veripy_declaring_dir"


def _tag_env_declaring_dir(config: dict, declaring_dir: Path) -> None:
    """Remember which config file declared each executionEnvironment, so its
    relative root can later be resolved against the declaring directory."""
    envs = config.get("executionEnvironments")
    if isinstance(envs, list):
        for env in envs:
            if isinstance(env, dict):
                env.setdefault(_DECLARING_DIR_KEY, str(declaring_dir))


def _load_config(config_dir: Path) -> dict | None:
    """The governing config as an effective dict (extends resolved); None if
    any part of it is unreadable — the caller fails closed on None."""
    cfg = config_dir / "pyrightconfig.json"
    if cfg.exists():
        return _resolve_extends(cfg, frozenset())
    pyproject = config_dir / "pyproject.toml"
    if pyproject.exists():
        try:
            data = tomllib.loads(pyproject.read_text(encoding="utf-8", errors="replace"))
        except (OSError, tomllib.TOMLDecodeError):
            return None
        for table in ("basedpyright", "pyright"):
            tool = data.get("tool", {}).get(table)
            if isinstance(tool, dict):
                _tag_env_declaring_dir(tool, config_dir)
                extends = tool.get("extends")
                if isinstance(extends, str):
                    base = _resolve_extends(config_dir / extends, frozenset())
                    if base is None:
                        return None
                    return {**base, **{k: v for k, v in tool.items() if k != "extends"}}
                return tool
    return {}


def _diagnostic_override_envs(
    config: dict, config_dir: Path, files: list[Path]
) -> dict[Path, str]:
    """Map each file covered by an executionEnvironment that overrides
    diagnostic settings to a description of the override."""
    flagged: dict[Path, str] = {}
    envs = config.get("executionEnvironments")
    if not isinstance(envs, list):
        return flagged
    for env in envs:
        if not isinstance(env, dict):
            continue
        overrides = sorted(set(env) - _ENV_STRUCTURAL_KEYS - {_DECLARING_DIR_KEY})
        root = env.get("root")
        if not overrides or not isinstance(root, str):
            continue
        # Resolve the root against BOTH the declaring config's directory and
        # the governing config's directory: coverage under either flags the
        # file. Over-approximating fails closed no matter which resolution
        # the checker actually applies for inherited environments.
        candidate_dirs = {config_dir}
        declaring = env.get(_DECLARING_DIR_KEY)
        if isinstance(declaring, str):
            candidate_dirs.add(Path(declaring))
        env_roots = {(d / root).resolve() for d in candidate_dirs}
        for path in files:
            if any(path == r or r in path.parents for r in env_roots):
                flagged[path] = (
                    f"executionEnvironment {root!r} overrides diagnostic "
                    f"settings ({', '.join(overrides)})"
                )
    return flagged


def run_type_gate(paths: list[Path], timeout: int = 300) -> TypeGateResult:
    exe = find_basedpyright()
    if exe is None:
        return TypeGateResult(
            available=False,
            error="basedpyright not found — install with `pip install 'veripy[types]'`",
        )

    # One invocation per governing config, run from that project's root, so
    # files from different projects are checked under their own settings.
    groups: dict[Path | None, list[Path]] = {}
    for path in paths:
        resolved = path.resolve()
        groups.setdefault(_governing_config_dir(resolved), []).append(resolved)

    diagnostics: list[TypeDiagnostic] = []
    version: str | None = None
    for config_dir, group in groups.items():
        if config_dir is not None:
            config = _load_config(config_dir)
            if config is None:
                diagnostics.extend(
                    TypeDiagnostic(
                        file=str(p),
                        line=1,
                        severity="error",
                        message=(
                            f"the governing pyright config in {config_dir} (or a "
                            f"config it extends) is unreadable; the VeriPy type "
                            f"gate fails closed — fix the config, or skip type "
                            f"checking explicitly with --no-types"
                        ),
                        rule="veripy-strict-required",
                    )
                    for p in group
                )
                continue
            flagged = _diagnostic_override_envs(config, config_dir, group)
            for path, reason in flagged.items():
                diagnostics.append(
                    TypeDiagnostic(
                        file=str(path),
                        line=1,
                        severity="error",
                        message=(
                            f"{reason} in {config_dir}; the VeriPy type gate "
                            f"cannot certify strictness under path-specific "
                            f"diagnostic overrides — remove them for gated "
                            f"files, or skip type checking with --no-types"
                        ),
                        rule="veripy-strict-required",
                    )
                )
            group = [p for p in group if p not in flagged]
            if not group:
                continue
            mode = config.get("typeCheckingMode")
            if mode is not None and (not isinstance(mode, str) or mode not in _STRICT_OK_MODES):
                # A weak project config cannot lower the gate: fail these
                # files explicitly rather than checking them meaninglessly.
                diagnostics.extend(
                    TypeDiagnostic(
                        file=str(p),
                        line=1,
                        severity="error",
                        message=(
                            f"governing pyright config ({config_dir}) sets "
                            f"typeCheckingMode={mode!r}; the VeriPy type gate "
                            f"requires 'strict' or stricter — raise the mode, "
                            f"or skip type checking explicitly with --no-types"
                        ),
                        rule="veripy-strict-required",
                    )
                    for p in group
                )
                continue
        cwd = config_dir or Path(os.path.commonpath([str(p.parent) for p in group]))
        cmd = [exe, "--outputjson", *[str(p) for p in group]]
        try:
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout, cwd=str(cwd)
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return TypeGateResult(available=False, error=f"basedpyright failed to run: {exc}")
        try:
            payload = json.loads(proc.stdout)
        except json.JSONDecodeError:
            return TypeGateResult(
                available=False,
                error=(
                    f"unparseable basedpyright output (exit {proc.returncode}): "
                    f"{proc.stdout[:200]!r} {proc.stderr[:200]!r}"
                ),
            )
        version = payload.get("version", version)
        diagnostics.extend(
            TypeDiagnostic(
                file=d.get("file", "?"),
                line=d.get("range", {}).get("start", {}).get("line", 0) + 1,
                severity=d.get("severity", "error"),
                message=d.get("message", ""),
                rule=d.get("rule"),
            )
            for d in payload.get("generalDiagnostics", [])
        )
    return TypeGateResult(available=True, version=version, diagnostics=diagnostics)
