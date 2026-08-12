"""Type gate: run basedpyright over files and surface its diagnostics.

ARCHITECTURE §3's conformance front-end is two passes: **basedpyright strict**
(solves dynamic *typing*; version-pinned and trusted, assumption A7) followed
by the AST allowlist pass (solves dynamic *semantics*). This module wires the
first pass into `lemmapy check`: a file's functions are not clean unless
basedpyright reports zero errors for that file.

Strictness comes from the governing pyright configuration — pyright applies
the nearest `pyrightconfig.json` even to explicitly listed files. LemmaPy
projects are expected to set `"typeCheckingMode": "strict"` (this repo's own
config does). If basedpyright is not installed the gate degrades to a visible
"skipped" notice, never a silent pass.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
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


def run_type_gate(paths: list[Path], timeout: int = 300) -> TypeGateResult:
    exe = find_basedpyright()
    if exe is None:
        return TypeGateResult(
            available=False,
            error="basedpyright not found — install with `pip install 'lemmapy[types]'`",
        )
    cmd = [exe, "--outputjson", *[str(p) for p in paths]]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
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
    diagnostics = [
        TypeDiagnostic(
            file=d.get("file", "?"),
            line=d.get("range", {}).get("start", {}).get("line", 0) + 1,
            severity=d.get("severity", "error"),
            message=d.get("message", ""),
            rule=d.get("rule"),
        )
        for d in payload.get("generalDiagnostics", [])
    ]
    return TypeGateResult(
        available=True, version=payload.get("version"), diagnostics=diagnostics
    )
