"""Lean driver: run `lean --json` on an emitted artifact and map results
back to Python source lines.

No lake, no project, no dependencies: slice 1's prelude is core-only, so
a bare `lean --json file.lean` elaboration is the whole prover run —
seconds, not a cold build (the ROADMAP's latency risk, retired for this
slice).
"""

from __future__ import annotations

import re

import functools
import json
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from ..dafny.driver import _map_line

# Message text -> published taxonomy kind. Checked in order; first hit
# wins. Every value must be a member of veripy/failures.py's taxonomy —
# tests/test_failures.py scans the package and fails on an undocumented
# kind. `unsolved goals` is the fixed tactic script failing to discharge
# the spec theorem: in this slice the theorem IS the ensures contract, so
# the kind is `postcondition`.
_KINDS: tuple[tuple[str, str], ...] = (
    ("unknown identifier", "resolution"),
    ("unknown constant", "resolution"),
    ("unsolved goals", "postcondition"),
    # `omega` failing on the spec theorem, pinned from live 4.33 output:
    # "omega could not prove the goal: ...". The theorem IS the ensures
    # contract in this slice, so the kind is `postcondition`.
    ("could not prove the goal", "postcondition"),
    ("omega could not prove", "postcondition"),
    ("maximum recursion depth", "timeout"),
    ("maxheartbeats", "timeout"),
    ("deterministic timeout", "timeout"),
    # The endgame combinator (`first | omega | trivial`) reports its last
    # sub-tactic's failure ("Tactic `assumption` failed") rather than
    # omega's phrasing — pinned from live output after the slice-2
    # cocktail change reclassified false specs as unknown. The turnstile
    # needle is the robust form: ANY diagnostic displaying an unsolved
    # goal is the spec theorem failing, whatever tactic reported it.
    ("tactic `assumption` failed", "postcondition"),
    ("depends on disallowed axioms", "axiom-footprint"),
    ("⊢", "postcondition"),
)


# The only axioms a proof may rest on. These three are Lean's own
# classical foundations, present in ordinary mathematics and trusted by
# the kernel. Anything else — above all `sorryAx`, which both `sorry`
# and `admit` introduce — means the "proof" was never checked.
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

_AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


def axiom_violations(messages: list[str]) -> list[tuple[str, list[str]]]:
    """(theorem, offending axioms) for every `#print axioms` line whose
    footprint escapes ALLOWED_AXIOMS.

    This is the semantic no-assumption guarantee: a syntactic whitelist
    can only approximate it, because it has to enumerate the ways a
    proof might cheat, while the footprint simply reports what the
    proof actually used."""
    out: list[tuple[str, list[str]]] = []
    for msg in messages:
        m = _AXIOM_LINE.search(msg)
        if not m:
            continue
        used = [a.strip() for a in m.group(2).split(",") if a.strip()]
        bad = [a for a in used if a not in ALLOWED_AXIOMS]
        if bad:
            out.append((m.group(1), bad))
    return out


def classify_lean_message(message: str) -> str:
    lowered = message.lower()
    for needle, kind in _KINDS:
        if needle in lowered:
            return kind
    return "unknown"


@dataclass
class LeanDiagnostic:
    # `dafny_line` is the payload schema's artifact-coordinate name
    # (veripy-failures/1 pins it; see DiagnosticLike) — it holds the
    # LEAN artifact line here until the AGENT-INTERFACE versions a
    # neutral name.
    dafny_line: int
    py_line: int | None
    severity: str
    message: str

    @property
    def obligation(self) -> str:
        return classify_lean_message(self.message)


@dataclass
class LeanVerifyResult:
    ok: bool
    diagnostics: list[LeanDiagnostic] = field(default_factory=list)
    summary: str = ""
    raw: str = ""
    error: str | None = None  # tool-level failure (lean missing/crashed)


def find_lean() -> str | None:
    return shutil.which("lean")


@functools.lru_cache(maxsize=1)
def lean_version() -> str | None:
    """The prover's own version string (provenance; cached per process,
    same contract as `dafny_version`)."""
    exe = find_lean()
    if exe is None:
        return None
    try:
        proc = subprocess.run([exe, "--version"], capture_output=True,
                              text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    first = (proc.stdout or proc.stderr).strip().splitlines()
    if not first:
        return None
    # "Lean (version 4.x.y, ...)" -> "4.x.y, ..." stays informative;
    # strip only the redundant product prefix.
    version = first[0].strip()
    for prefix in ("Lean (version ", "Lean "):
        if version.startswith(prefix):
            version = version[len(prefix):].rstrip(")").strip()
            break
    return version or None


def parse_lean_json(stdout: str) -> list[dict]:
    """`lean --json` emits one JSON object per line; tolerate non-JSON
    interleavings (progress lines) rather than dying on them."""
    out = []
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            out.append(obj)
    return out


def verify_lean_file(path: Path, line_map: dict[int, int],
                     time_limit: int = 30,
                     stub_extent: int | None = None) -> LeanVerifyResult:
    exe = find_lean()
    if exe is None:
        return LeanVerifyResult(ok=False, error="lean not found on PATH")
    try:
        # Lean's own budget is heartbeats, not seconds; the wall guards a
        # hung process, generously (same shape as the Dafny driver's).
        proc = subprocess.run([exe, "--json", str(path)],
                              capture_output=True, text=True,
                              timeout=time_limit * 20 + 120)
    except (OSError, subprocess.TimeoutExpired) as exc:
        return LeanVerifyResult(ok=False, error=f"lean failed to run: {exc}")
    output = proc.stdout + proc.stderr
    diagnostics: list[LeanDiagnostic] = []
    for obj in parse_lean_json(proc.stdout):
        severity = str(obj.get("severity", "error")).lower()
        pos = obj.get("pos") or {}
        lean_line = int(pos.get("line") or 0)
        message = str(obj.get("data") or obj.get("message") or "")
        diagnostics.append(LeanDiagnostic(
            dafny_line=lean_line,
            py_line=_map_line(line_map, lean_line, stub_extent),
            severity=severity,
            message=message,
        ))
    errors = [d for d in diagnostics if d.severity == "error"]
    if proc.returncode != 0 and not errors:
        # Nonzero exit with NO parsed error diagnostic is the tool
        # failing (crash, bad invocation, stderr-only complaint), not a
        # proof failing. Reporting it as `failed` would fabricate an
        # `unknown` proof obligation and send a repair loop after a
        # proof that was never judged — a tool error in a proof-failure
        # costume, the exact conflation the taxonomy exists to prevent.
        return LeanVerifyResult(
            ok=False, diagnostics=diagnostics, raw=output,
            error=(f"lean exited {proc.returncode} without diagnostics: "
                   f"{(proc.stderr or proc.stdout)[:400]}"))
    ok = proc.returncode == 0 and not errors
    # A proof that elaborated is not yet a proof that was CHECKED. Lean
    # reports each theorem's axiom footprint, and anything outside the
    # allowed set means the evidence rests on something the kernel
    # never verified — `sorryAx` above all, which is what both `sorry`
    # and `admit` leave behind. A syntactic whitelist has to enumerate
    # the ways a proof might cheat; this reports what it actually used.
    if ok:
        violations = axiom_violations([d.message for d in diagnostics])
        for thm, bad in violations:
            diagnostics.append(LeanDiagnostic(
                dafny_line=0, py_line=None, severity="error",
                message=(f"theorem {thm!r} depends on disallowed axioms "
                         f"{bad} — the proof was not kernel-checked"),
            ))
        if violations:
            ok = False
            errors = [d for d in diagnostics if d.severity == "error"]
    summary = (f"lean finished with {len(errors)} error(s)"
               if diagnostics or proc.returncode else "lean finished clean")
    return LeanVerifyResult(ok=ok, diagnostics=diagnostics,
                            summary=summary, raw=output)
