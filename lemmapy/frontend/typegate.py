"""Type gate: run basedpyright over files and surface its diagnostics.

ARCHITECTURE §3's conformance front-end is two passes: **basedpyright strict**
(solves dynamic *typing*; version-pinned and trusted, assumption A7) followed
by the AST allowlist pass (solves dynamic *semantics*). This module wires the
first pass into `lemmapy check`: a file's functions are not clean unless
basedpyright reports zero errors for that file.

Project settings come from the governing pyright configuration: files are
grouped by their nearest `pyrightconfig.json` (or `pyproject.toml` with a
[tool.pyright]/[tool.basedpyright] table) and each group is checked in its own
project context, so one command spanning several projects applies each
project's settings — **except weakness**. A config whose `typeCheckingMode`
is weaker than "strict" cannot lower the gate: those files fail with a
`lemmapy-strict-required` diagnostic instead of being checked meaninglessly.
An unset mode is acceptable because basedpyright's default ("recommended") is
stricter than "strict". (Per-execution-environment mode overrides inside the
config are not inspected — an M0 approximation.) If basedpyright cannot run,
the gate reports unavailable and `lemmapy check` FAILS — skipping type
analysis is only possible via the explicit `--no-types` opt-out.
"""

from __future__ import annotations

import json
import os
import re
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


def _config_mode(config_dir: Path) -> str | None:
    """The governing config's typeCheckingMode; None if unset (basedpyright's
    default "recommended" then applies); "<unreadable>" if the config cannot
    be parsed (treated as failing the gate — fail closed)."""
    cfg = config_dir / "pyrightconfig.json"
    if cfg.exists():
        try:
            text = cfg.read_text(encoding="utf-8", errors="replace")
            text = re.sub(r"^\s*//.*$", "", text, flags=re.M)  # pyright allows comments
            data = json.loads(text)
        except (OSError, json.JSONDecodeError):
            return "<unreadable>"
        mode = data.get("typeCheckingMode")
        return mode if isinstance(mode, str) else None
    pyproject = config_dir / "pyproject.toml"
    if pyproject.exists():
        try:
            data = tomllib.loads(pyproject.read_text(encoding="utf-8", errors="replace"))
        except (OSError, tomllib.TOMLDecodeError):
            return "<unreadable>"
        for table in ("basedpyright", "pyright"):
            tool = data.get("tool", {}).get(table, {})
            if isinstance(tool, dict) and "typeCheckingMode" in tool:
                return str(tool["typeCheckingMode"])
        return None
    return None


def run_type_gate(paths: list[Path], timeout: int = 300) -> TypeGateResult:
    exe = find_basedpyright()
    if exe is None:
        return TypeGateResult(
            available=False,
            error="basedpyright not found — install with `pip install 'lemmapy[types]'`",
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
            mode = _config_mode(config_dir)
            if mode is not None and mode not in _STRICT_OK_MODES:
                # A weak project config cannot lower the gate: fail these
                # files explicitly rather than checking them meaninglessly.
                diagnostics.extend(
                    TypeDiagnostic(
                        file=str(p),
                        line=1,
                        severity="error",
                        message=(
                            f"governing pyright config ({config_dir}) sets "
                            f"typeCheckingMode={mode!r}; the LemmaPy type gate "
                            f"requires 'strict' or stricter — raise the mode, "
                            f"or skip type checking explicitly with --no-types"
                        ),
                        rule="lemmapy-strict-required",
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
