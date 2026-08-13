"""The verification report (ARCHITECTURE §5): the artifact that makes the
guarantee honest. Per-function verdicts, the island assumptions A1–A7
verbatim with their discharge status, per-boundary clause enumeration, the
trusted-contract count, and the guard mode per entry point."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any

from .backends.dafny.preamble import PREAMBLE_VERSION

# A1–A7 verbatim from ARCHITECTURE §5, with the current discharge status.
# "assumed" = trusted, stated; "partially-discharged" = tooling removes the
# common cases, the residual is stated in `residual`.
ASSUMPTIONS: list[dict[str, str]] = [
    {
        "id": "A1",
        "text": "Island definitions and the builtins they reference are as "
                "verified: no patching of `builtins`, no ctypes/gc/frame "
                "manipulation.",
        "status": "partially-discharged",
        "residual": "The guarded module carries a verbatim island copy with a "
                    "SHA-256 (on-disk tampering detectable via "
                    "verify_island_integrity) and wrappers bind the island and "
                    "helpers in closure cells at definition time (module-attribute "
                    "rebinding cannot redirect them); direct closure-cell surgery "
                    "and builtins patching remain assumed absent.",
    },
    {
        "id": "A2",
        "text": "All external entries pass through generated guards (no "
                "imports of _-prefixed internals).",
        "status": "assumed",
        "residual": "`lemmapy guard` emits the boundary; nothing prevents a "
                    "caller from importing the original module — that is the "
                    "documented trusted-caller elision path.",
    },
    {
        "id": "A3",
        "text": "No concurrent mutation of island-reachable data during "
                "island execution.",
        "status": "partially-discharged",
        "residual": "Copy-in gives the island private fresh containers; the "
                    "residual covers the guard's own traversal window and "
                    "future Tier-3 extern calls.",
    },
    {
        "id": "A4",
        "text": "A pinned CPython version range implements the modeled "
                "builtins per the fragment semantics.",
        "status": "assumed",
        "residual": "Continuously cross-checked by the differential harness "
                    "(lemmapy difftest) on every corpus function.",
    },
    {
        "id": "A5",
        "text": "Asynchronous exceptions and resource exhaustion "
                "(KeyboardInterrupt, MemoryError, RecursionError) are outside "
                "the model: properties are partial correctness modulo them.",
        "status": "assumed",
        "residual": "",
    },
    {
        "id": "A6",
        "text": "No import-system or encoding-level tampering (sys.modules "
                "replacement, path hooks).",
        "status": "assumed",
        "residual": "",
    },
    {
        "id": "A7",
        "text": "The pinned basedpyright version's type judgments on accepted "
                "files are correct.",
        "status": "assumed",
        "residual": "The type gate is fail-closed (`--no-types` is an explicit "
                    "opt-out, never a silent skip).",
    },
]


@dataclass
class FunctionReport:
    name: str
    file: str
    line: int
    status: str  # verified | failed | error | not-run
    marked_verified: bool
    requires: list[str] = field(default_factory=list)
    ensures: list[str] = field(default_factory=list)
    proof_clauses: list[str] = field(default_factory=list)
    failures: list[dict[str, Any]] = field(default_factory=list)
    # Every requires in the frozen grammar is executable, so the assumed
    # (non-executable) clause set at the boundary is empty by construction.
    assumed_clauses: list[str] = field(default_factory=list)
    guard_mode: str = "guarded module available via `lemmapy guard`; trusted callers import the original"


def function_report(spec: Any, file: str, status: str,
                    failures: list[dict[str, Any]] | None = None) -> FunctionReport:
    return FunctionReport(
        name=spec.name,
        file=file,
        line=spec.lineno,
        status=status,
        marked_verified=spec.verified,
        requires=[c.raw for c in spec.by_kind("requires")],
        ensures=[c.raw for c in spec.by_kind("ensures")],
        proof_clauses=[c.raw for c in spec.by_kind("proof")],
        failures=failures or [],
    )


def build_report(functions: list[FunctionReport], sidecar_lemmas: dict[str, list[str]],
                 dafny_version: str | None) -> dict[str, Any]:
    verified = [f for f in functions if f.status == "verified"]
    return {
        "schema": "lemmapy-verification-report/1",
        "preamble_version": PREAMBLE_VERSION,
        "dafny_version": dafny_version,
        "summary": {
            "functions": len(functions),
            "verified": len(verified),
            "failed": sum(1 for f in functions if f.status == "failed"),
            "errors": sum(1 for f in functions if f.status == "error"),
            # Tier-3 externs are not implemented yet, so the guarantee is
            # "verified modulo 0 trusted contracts" — computed, not asserted.
            "trusted_contracts": 0,
        },
        "functions": [asdict(f) for f in functions],
        "sidecar_lemmas": sidecar_lemmas,
        "assumptions": ASSUMPTIONS,
    }


def render_report_text(report: dict[str, Any]) -> str:
    s = report["summary"]
    lines = [
        f"verification report (preamble {report['preamble_version']}, "
        f"dafny {report['dafny_version'] or 'not run'})",
        f"  functions: {s['functions']}  verified: {s['verified']}  "
        f"failed: {s['failed']}  errors: {s['errors']}",
        f"  guarantee: verified modulo {s['trusted_contracts']} trusted contracts",
    ]
    for f in report["functions"]:
        mark = "[verified]" if f["marked_verified"] else "[spec'd]"
        lines.append(
            f"  {f['name']} {mark} {f['status']}: "
            f"{len(f['requires'])} requires (all executable), "
            f"{len(f['ensures'])} ensures, {len(f['proof_clauses'])} proof clauses"
        )
        for failure in f["failures"]:
            lines.append(f"    {failure.get('file')}:{failure.get('line')}: {failure.get('message')}")
    lines.append("  assumptions:")
    for a in report["assumptions"]:
        lines.append(f"    {a['id']} [{a['status']}] {a['text']}")
    return "\n".join(lines)
