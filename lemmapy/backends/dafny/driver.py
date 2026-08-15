"""Verifier driver: run `dafny verify` on an emitted stub and map results
back to Python source lines."""

from __future__ import annotations

import functools
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

_DIAG_RE = re.compile(r"^(?P<file>.+?\.dfy)\((?P<line>\d+),(?P<col>\d+)\): (?P<sev>Error|Warning)(?::| ) ?(?P<msg>.*)$")
_RELATED_RE = re.compile(r"^(?P<file>.+?\.dfy)\((?P<line>\d+),(?P<col>\d+)\): Related location: ?(?P<msg>.*)$")
_SUMMARY_RE = re.compile(r"finished with (?P<ok>\d+) verified, (?P<bad>\d+) error")


# Obligation classification: Dafny's message text -> the kind of proof
# obligation that failed. Every value here must be a member of the
# published taxonomy (lemmapy/failures.py PROVER_KINDS) — that is what a
# host branches on, and tests/test_failures.py fails if this drifts.
_OBLIGATION_KINDS: tuple[tuple[str, str], ...] = (
    ("postcondition", "postcondition"),
    ("loop invariant", "invariant"),
    ("assertion", "assertion"),
    ("precondition for this call", "call-precondition"),
    ("requires clause", "call-precondition"),
    ("decreases", "termination"),
    ("timed out", "timeout"),
    ("out of resource", "timeout"),
    # Resolution/type errors in the (engine- or hand-written) sidecar: the
    # proof was never attempted, so they are not obligations. Checked
    # before the obligation patterns because their text can mention one.
    ("unresolved identifier", "resolution"),
    ("wrong number of arguments", "resolution"),
    ("incorrect argument type", "resolution"),
    ("duplicate name", "resolution"),
    ("index out of range", "bounds"),
    ("divisor is always non-zero", "division"),
)


def classify_obligation(message: str) -> str:
    lowered = message.lower()
    for needle, kind in _OBLIGATION_KINDS:
        if needle in lowered:
            return kind
    return "unknown"


@dataclass
class Diagnostic:
    dafny_line: int
    py_line: int | None
    severity: str
    message: str

    @property
    def obligation(self) -> str:
        return classify_obligation(self.message)


@dataclass
class VerifyResult:
    ok: bool
    diagnostics: list[Diagnostic] = field(default_factory=list)
    summary: str = ""
    raw: str = ""
    error: str | None = None  # tool-level failure (dafny missing/crashed)


def find_dafny() -> str | None:
    return shutil.which("dafny")


@functools.lru_cache(maxsize=1)
def dafny_version() -> str | None:
    """The prover's own version string, or None if it cannot be determined.

    Provenance in a verification report has to be the REAL version: a
    backend must be able to tell whether "verified" meant the same thing
    across two runs. (This field once held `result.summary` — "finished
    with N verified, 0 errors" — which is an outcome, not an identity.)
    Cached because it shells out and the answer cannot change mid-run."""
    exe = find_dafny()
    if exe is None:
        return None
    try:
        # `--version` is trivial (~0.1s); a longer wait means a broken or
        # stalled binary, and callers should not pay a minute for that.
        proc = subprocess.run([exe, "--version"], capture_output=True,
                              text=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    first = (proc.stdout or proc.stderr).strip().splitlines()
    if not first:
        return None
    # Builds differ: 4.11.0 prints a bare "4.11.0", others print
    # "Dafny version 4.x.y". Strip the redundant prefix so a renderer's own
    # "dafny " label cannot produce "dafny Dafny version 4.x.y".
    version = first[0].strip()
    for prefix in ("Dafny version ", "Dafny "):
        if version.startswith(prefix):
            version = version[len(prefix):].strip()
            break
    return version or None


def _map_line(line_map: dict[int, int], dafny_line: int,
              stub_extent: int | None = None) -> int | None:
    """Exact hit, else the nearest mapped line above (statements span lines).

    `stub_extent` is where the GENERATED region ends; everything past it is
    the appended proof sidecar, which has no Python line at all. Without the
    bound, the nearest-above fallback answers with the last mapped line in
    the file — so a failing lemma was reported against whichever Python
    statement happened to be encoded last, a line with nothing to do with
    it. Absent is the honest answer, and callers already handle None.
    """
    if stub_extent is not None and dafny_line > stub_extent:
        return None
    if dafny_line in line_map:
        return line_map[dafny_line]
    candidates = [dl for dl in line_map if dl < dafny_line]
    return line_map[max(candidates)] if candidates else None


def verify_dafny_file(
    path: Path, line_map: dict[int, int], time_limit: int = 30,
    stub_extent: int | None = None,
) -> VerifyResult:
    exe = find_dafny()
    if exe is None:
        return VerifyResult(ok=False, error="dafny not found on PATH")
    # --allow-warnings: the prover's VERDICT is the authority. Without it,
    # Dafny exits non-zero on style warnings (e.g. a triggerless forall in
    # an engine-authored sidecar) even after "N verified, 0 errors" — which
    # would surface as `failed` with zero failure records, a payload no
    # repair loop can act on.
    cmd = [exe, "verify", "--allow-warnings",
           "--verification-time-limit", str(time_limit), str(path)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=time_limit * 20 + 120)
    except (OSError, subprocess.TimeoutExpired) as exc:
        return VerifyResult(ok=False, error=f"dafny failed to run: {exc}")
    output = proc.stdout + proc.stderr
    diagnostics: list[Diagnostic] = []
    for raw_line in output.splitlines():
        stripped = raw_line.strip()
        related = _RELATED_RE.match(stripped)
        if related and diagnostics:
            # Dafny reports e.g. a failing postcondition at the return path,
            # with the actual ensures clause in a Related location line —
            # fold it into the previous diagnostic so the report points at
            # the spec clause, not just the return statement.
            rline = int(related.group("line"))
            r_py = _map_line(line_map, rline, stub_extent)
            last = diagnostics[-1]
            if r_py is not None:
                last.message += f" (related: source line {r_py})"
                if last.py_line is None:
                    last.py_line = r_py
            continue
        m = _DIAG_RE.match(stripped)
        if m:
            dline = int(m.group("line"))
            diagnostics.append(Diagnostic(
                dafny_line=dline,
                py_line=_map_line(line_map, dline, stub_extent),
                severity=m.group("sev").lower(),
                message=m.group("msg").strip(),
            ))
    summary_match = _SUMMARY_RE.search(output)
    summary = summary_match.group(0) if summary_match else ""
    ok = proc.returncode == 0
    if not ok and not diagnostics and not summary:
        return VerifyResult(ok=False, error=f"dafny exited {proc.returncode}: {output[:400]}", raw=output)
    return VerifyResult(ok=ok, diagnostics=diagnostics, summary=summary, raw=output)
