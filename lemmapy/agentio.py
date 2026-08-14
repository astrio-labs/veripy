"""The agent interface (M2): machine-actionable verification outcomes.

`verify_structured` is the API the proof-repair loop consumes and the
substance of `lemmapy verify --json`: per-failure records carrying the
obligation kind, both coordinate systems (Python and Dafny lines), the
function attribution, and the current proof-sidecar state — everything an
agent needs to act without re-parsing human-oriented output.
"""

from __future__ import annotations

import json
import tempfile
from pathlib import Path
from tokenize import TokenError
from typing import Any

from .backends.dafny.driver import verify_dafny_file
from .backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar
from .frontend.extract import parse_source

SCHEMA = "lemmapy-failures/1"


def _attribute(specs: Any, py_line: int | None) -> str | None:
    """Enclosing function by source span (functions are module-level and
    non-overlapping — enforced by the encoder)."""
    if py_line is None:
        return None
    best = None
    for fn in sorted(specs.functions, key=lambda f: f.lineno):
        if fn.lineno <= py_line:
            best = fn.name
        else:
            break
    return best


def verify_structured(path: Path, outdir: Path, time_limit: int = 30,
                      hunt_counterexamples: bool = False) -> dict[str, Any]:
    """Encode + verify one module; return the structured outcome. Never
    raises for expected failure modes — every outcome is a payload.

    Every invocation stages into a PRIVATE directory under `outdir`. The
    stub used to be written to `outdir/<stem>.dfy`, so two concurrent
    verifications of same-stemmed modules sharing an outdir raced on one
    file: whichever wrote last was the one Dafny actually read. Both
    directions were silent and well-formed — a module that violates its
    spec came back `ok` (unverified code reported verified), and a correct
    module came back `failed` with failures belonging to the other file.
    An embedding host naturally shares one scratch directory across
    callers, so this is a soundness break, not a tidiness issue.
    """
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "file": str(path),
        "status": None,
        "functions": [],
        "failures": [],
        "sidecar": None,
    }
    try:
        outdir.mkdir(parents=True, exist_ok=True)
        # mkdtemp is atomic and unique per process AND per thread, which a
        # stem- or PID-derived name is not.
        workdir = Path(tempfile.mkdtemp(prefix="verify-", dir=outdir))
        source = path.read_text()
    except (OSError, UnicodeDecodeError) as exc:
        payload["status"] = "tool-error"
        payload["error"] = f"unreadable source: {exc}"
        return payload
    try:
        specs = parse_source(source, filename=str(path))
    except SyntaxError as exc:
        payload["status"] = "spec-error"
        payload["failures"] = [
            {"kind": "syntax", "py_line": exc.lineno, "message": exc.msg}
        ]
        return payload
    except (ValueError, TokenError) as exc:
        # Null bytes raise ValueError on older Pythons; the comment
        # tokenizer raises TokenError on some malformed buffers.
        payload["status"] = "spec-error"
        payload["failures"] = [
            {"kind": "syntax", "py_line": None, "message": str(exc)}
        ]
        return payload
    payload["functions"] = [fn.name for fn in specs.functions]
    if specs.errors or specs.orphans:
        payload["status"] = "spec-error"
        payload["failures"] = [
            {"kind": "spec", "py_line": c.line, "message": c.error}
            for c in [*specs.errors, *specs.orphans] if c.error
        ]
        return payload
    try:
        sidecar = load_proof_sidecar(path)
        encoded = encode_module(source, specs, module_name=path.name,
                                proof_lemmas=sidecar.lemmas)
    except EncodeError as exc:
        payload["status"] = "encode-error"
        payload["failures"] = [
            {"kind": "conformance", "py_line": exc.line, "message": exc.message}
        ]
        return payload
    except (OSError, UnicodeDecodeError) as exc:
        payload["status"] = "tool-error"
        payload["error"] = f"unreadable proof sidecar: {exc}"
        return payload
    sidecar_path = path.with_name(path.stem + ".proofs.dfy")
    payload["sidecar"] = {
        "path": str(sidecar_path),
        "exists": sidecar_path.exists(),
        "lemmas": sorted(sidecar.lemmas),
        "text": sidecar.text,
    }
    stub = workdir / f"{path.stem}.dfy"
    try:
        stub.write_text(encoded.dafny_source + sidecar.text)
    except OSError as exc:
        payload["status"] = "tool-error"
        payload["error"] = f"cannot write stub: {exc}"
        return payload
    payload["stub"] = str(stub)
    stub_extent = encoded.dafny_source.count("\n") + 1
    result = verify_dafny_file(stub, encoded.line_map, time_limit=time_limit)
    if result.error is not None:
        payload["status"] = "tool-error"
        payload["error"] = result.error
        return payload
    if result.ok:
        payload["status"] = "ok"
        return payload
    payload["status"] = "failed"
    for d in result.diagnostics:
        if d.severity != "error":
            continue
        in_sidecar = d.dafny_line > stub_extent
        failure: dict[str, Any] = {
            "kind": d.obligation,
            "function": None if in_sidecar else _attribute(specs, d.py_line),
            "region": "sidecar" if in_sidecar else "source",
            "py_line": None if in_sidecar else d.py_line,
            "dafny_line": d.dafny_line,
            "message": d.message,
        }
        payload["failures"].append(failure)
    if not payload["failures"]:
        # A failed run must never carry an EMPTY failure list — an engine
        # (or a person) needs something actionable. Belt-and-braces: with
        # --allow-warnings in the driver this path should be unreachable.
        payload["failures"].append({
            "kind": "unknown", "function": None, "region": "source",
            "py_line": None, "dafny_line": None,
            "message": (result.summary or result.raw[:400]
                        or "verifier failed without diagnostics"),
        })
    if hunt_counterexamples and payload["failures"]:
        from .benchmark.runner import _hunt

        # Also private: _hunt stages `<stem>_checked.py`, which collides on
        # exactly the same stems the stub did.
        verdict, detail = _hunt(source, path.stem, workdir / "hunt", 5)
        if verdict == "counterexample":
            payload["counterexample"] = detail
    return payload


def verify_structured_many(paths: list[Path], outdir: Path, time_limit: int = 30,
                           hunt_counterexamples: bool = False) -> list[dict[str, Any]]:
    """Same-stem inputs no longer need special handling: `verify_structured`
    stages each invocation privately, so stub paths are unique by
    construction — across calls, threads and processes, not just within
    one batch as the old `dup{n}` scheme managed."""
    return [
        verify_structured(p, outdir, time_limit=time_limit,
                          hunt_counterexamples=hunt_counterexamples)
        for p in paths
    ]


def dump(payloads: list[dict[str, Any]], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payloads, indent=1))
