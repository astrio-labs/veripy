"""The agent interface (M2): machine-actionable verification outcomes.

`verify_structured` is the API the proof-repair loop consumes and the
substance of `lemmapy verify --json`: per-failure records carrying the
obligation kind, both coordinate systems (Python and Dafny lines), the
function attribution, and the current proof-sidecar state — everything an
agent needs to act without re-parsing human-oriented output.
"""

from __future__ import annotations

import json
from pathlib import Path
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
    raises for expected failure modes — every outcome is a payload."""
    outdir.mkdir(parents=True, exist_ok=True)
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "file": str(path),
        "status": None,
        "functions": [],
        "failures": [],
        "sidecar": None,
    }
    try:
        source = path.read_text()
    except OSError as exc:
        payload["status"] = "tool-error"
        payload["error"] = f"unreadable source: {exc}"
        return payload
    specs = parse_source(source, filename=str(path))
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
    stub = outdir / f"{path.stem}.dfy"
    stub.write_text(encoded.dafny_source + sidecar.text)
    payload["stub"] = str(stub)
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
        failure: dict[str, Any] = {
            "kind": d.obligation,
            "function": _attribute(specs, d.py_line),
            "py_line": d.py_line,
            "dafny_line": d.dafny_line,
            "message": d.message,
        }
        payload["failures"].append(failure)
    if hunt_counterexamples and payload["failures"]:
        from .benchmark.runner import _hunt

        verdict, detail = _hunt(source, path.stem, outdir / "hunt", 5)
        if verdict == "counterexample":
            payload["counterexample"] = detail
    return payload


def verify_structured_many(paths: list[Path], outdir: Path, time_limit: int = 30,
                           hunt_counterexamples: bool = False) -> list[dict[str, Any]]:
    return [
        verify_structured(p, outdir, time_limit=time_limit,
                          hunt_counterexamples=hunt_counterexamples)
        for p in paths
    ]


def dump(payloads: list[dict[str, Any]], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payloads, indent=1))
