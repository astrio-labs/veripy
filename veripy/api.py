"""The embedding surface: what a host program calls.

`import veripy` gives a host four operations and one provenance query.
Everything else in the package is internal and may be reshaped.

The CLI is *a client of this module*, not the other way round. That
direction matters: today's entry points are nine `cmd_*` functions that
print to stdout and return exit codes, which a host embedding VeriPy as a
proof backend cannot use — it needs values, not console output, and a
library that calls `sys.exit` or writes to stdout is unusable inside
someone else's process.

Three properties this module guarantees, each pinned by a test:

1. **It never prints.** Diagnostics are returned, not emitted.
2. **It never exits.** No `sys.exit`, no `SystemExit`.
3. **Expected failures are values.** A file outside the fragment, an
   unparseable one, an unreadable path, a workdir the host cannot write, a
   missing prover — all return a payload with a `status`, never an
   exception. Exceptions are reserved for programmer error (a wrong
   argument type), which a host should not catch.

Payload shapes and the failure vocabulary are documented in
docs/AGENT-INTERFACE.md and versioned by `toolchain_info()`.
"""

from __future__ import annotations

from pathlib import Path
from tokenize import TokenError
from typing import Any

from .agentio import verify_structured
from .backends.dafny.driver import dafny_version
from .backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar
from .backends.dafny.preamble import PREAMBLE_VERSION
from .failures import FAILURE_KINDS, TAXONOMY_VERSION
from .frontend.extract import parse_source

__all__ = [
    "conformance",
    "verify",
    "repair",
    "guard",
    "toolchain_info",
]


def toolchain_info() -> dict[str, Any]:
    """Versions a host can compare across runs, plus the failure vocabulary.

    A backend that cannot say what produced a verdict cannot be trusted to
    have produced the same verdict twice.
    """
    return {
        "preamble_version": PREAMBLE_VERSION,
        "dafny_version": dafny_version(),
        "taxonomy_version": TAXONOMY_VERSION,
        "failure_kinds": sorted(FAILURE_KINDS),
    }


def conformance(path: Path | str) -> dict[str, Any]:
    """Is this module inside the verified fragment?

    The cheap gate: no prover, no type checker, no subprocess. A host can
    call this on every candidate file and only pay for `verify` on the
    ones that would survive it.

    Returns `{"conformant": bool, "functions": [...], "failures": [...]}`,
    where each failure carries a published `kind` and a source line.
    """
    path = Path(path)
    try:
        source = path.read_text()
    except (OSError, UnicodeDecodeError) as exc:
        return {"conformant": False, "functions": [],
                "failures": [{"kind": "unknown", "py_line": None,
                              "message": f"unreadable source: {exc}"}]}
    try:
        specs = parse_source(source, filename=str(path))
    except SyntaxError as exc:
        return {"conformant": False, "functions": [],
                "failures": [{"kind": "syntax", "py_line": exc.lineno,
                              "message": exc.msg}]}
    except (ValueError, TokenError) as exc:
        # Null bytes (ValueError on older Pythons) and comment-tokenizer
        # failures on malformed buffers. Deliberately NOT a bare `Exception`:
        # swallowing everything here would turn a genuine bug in the parser
        # into a quiet "not conformant", which is the worst possible answer.
        return {"conformant": False, "functions": [],
                "failures": [{"kind": "syntax", "py_line": None,
                              "message": str(exc)}]}
    names = [fn.name for fn in specs.functions]
    if specs.errors or specs.orphans:
        return {"conformant": False, "functions": names,
                "failures": [{"kind": "spec", "py_line": c.line,
                              "message": c.error}
                             for c in [*specs.errors, *specs.orphans]
                             if c.error]}
    try:
        sidecar = load_proof_sidecar(path)
        encode_module(source, specs, module_name=path.name,
                      proof_lemmas=sidecar.lemmas)
    except EncodeError as exc:
        return {"conformant": False, "functions": names,
                "failures": [{"kind": "conformance", "py_line": exc.line,
                              "message": exc.message}]}
    except (OSError, UnicodeDecodeError) as exc:
        return {"conformant": False, "functions": names,
                "failures": [{"kind": "unknown", "py_line": None,
                              "message": f"unreadable proof sidecar: {exc}"}]}
    return {"conformant": True, "functions": names, "failures": []}


def verify(path: Path | str, workdir: Path | str, *, time_limit: int = 30,
           keep_artifacts: bool = False,
           backend: str = "dafny") -> dict[str, Any]:
    """Prove the module, returning the structured outcome.

    The payload is `veripy-failures/1` (docs/AGENT-INTERFACE.md): a
    `status`, per-failure records with a published `kind` and both
    coordinate systems, the sidecar's state, and `toolchain` provenance.
    Every outcome is a payload — prover crashes and unreadable files
    included. `backend` selects the proof backend (`dafny` today; the
    ROADMAP's Lean track lands behind the same name-based seam).
    """
    return verify_structured(Path(path), Path(workdir),
                             time_limit=time_limit,
                             keep_artifacts=keep_artifacts,
                             backend=backend)


def repair(path: Path | str, workdir: Path | str, *, engine: str = "claude",
           max_iterations: int = 4, time_limit: int = 30,
           apply: bool = False) -> dict[str, Any]:
    """Attempt to complete the proof by editing ONLY the proof sidecar.

    The engine cannot touch source or specs, so it cannot weaken what it
    was asked to prove. Returns `{"verified", "iterations", "reason",
    "sidecar_text"}`; `apply=True` writes a successful sidecar next to the
    source (previous content preserved as `.bak`).

    (The per-call engine wall is a separate change in flight; once it
    lands this grows an `engine_wall` argument rather than changing shape.)
    """
    from .repair import make_engine, repair_file

    path = Path(path)
    try:
        # repair_file stages a copy, so an unreadable source would raise
        # out of the library and into the host. Property 3 of this module:
        # expected failures are VALUES.
        path.read_text()
    except (OSError, UnicodeDecodeError) as exc:
        return {"verified": False, "iterations": 0,
                "reason": f"unreadable source: {exc}", "sidecar_text": None}
    try:
        eng = make_engine(engine)
    except ValueError as exc:
        return {"verified": False, "iterations": 0, "reason": str(exc),
                "sidecar_text": None}
    try:
        outcome = repair_file(path, Path(workdir), eng,
                              max_iterations=max_iterations,
                              time_limit=time_limit, apply=apply)
    except (OSError, UnicodeDecodeError) as exc:
        # Everything repair_file touches on disk is outside this library's
        # control: the workdir (a host may hand us a path that is a file, or
        # a directory it cannot write), the sidecar beside the source, and —
        # under apply=True — the source's own directory. Any of those is an
        # environment failure, not programmer error, so it is a VALUE.
        # Narrow on purpose: a TypeError from repair_file is our bug and
        # must still reach the host.
        return {"verified": False, "iterations": 0,
                "reason": f"filesystem error: {exc}", "sidecar_text": None}
    return {"verified": outcome.verified, "iterations": outcome.iterations,
            "reason": outcome.reason, "sidecar_text": outcome.sidecar_text}


def guard(path: Path | str, *, check_ensures: bool = False) -> dict[str, Any]:
    """Generate the boundary-guard module source for a verified module.

    Returned as TEXT rather than written to disk: where a host puts
    generated code is the host's decision, not this library's.
    """
    from .guards.emitter import GuardGenError, emit_guarded

    path = Path(path)
    try:
        source = path.read_text()
    except (OSError, UnicodeDecodeError) as exc:
        return {"ok": False, "source": None, "reason": f"unreadable: {exc}"}
    try:
        specs = parse_source(source, filename=str(path))
    except SyntaxError as exc:
        # Null bytes arrive as a SyntaxError with no lineno; naming a line
        # number of "None" would be worse than not naming one.
        where = f" on line {exc.lineno}" if exc.lineno else ""
        return {"ok": False, "source": None,
                "reason": f"syntax error{where}: {exc.msg}"}
    except (ValueError, TokenError) as exc:
        # Same non-SyntaxError parse failures conformance() enumerates (null
        # bytes, comment-tokenizer failures on a malformed buffer). A host
        # that guards a directory of candidate files hits these on the first
        # unparseable one, and a raised exception there kills the sweep.
        return {"ok": False, "source": None, "reason": f"unparseable: {exc}"}
    if specs.errors or specs.orphans:
        return {"ok": False, "source": None,
                "reason": "spec errors; call conformance() first"}
    try:
        text = emit_guarded(source, specs, src_name=path.name,
                            check_ensures=check_ensures)
    except GuardGenError as exc:
        return {"ok": False, "source": None, "reason": exc.message}
    return {"ok": True, "source": text, "reason": "generated"}
