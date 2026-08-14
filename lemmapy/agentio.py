"""The agent interface (M2): machine-actionable verification outcomes.

`verify_structured` is the API the proof-repair loop consumes and the
substance of `lemmapy verify --json`: per-failure records carrying the
obligation kind, both coordinate systems (Python and Dafny lines), the
function attribution, and the current proof-sidecar state — everything an
agent needs to act without re-parsing human-oriented output.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import tempfile
from pathlib import Path
from tokenize import TokenError
from typing import Any

from .backends.dafny.driver import dafny_version, verify_dafny_file
from .backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar
from .backends.dafny.preamble import PREAMBLE_VERSION
from .failures import TAXONOMY_VERSION
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


def new_payload(file: str, keep_artifacts: bool = False) -> dict[str, Any]:
    """The documented payload skeleton. EVERY producer must build on
    this — the contract promises `toolchain` on every outcome, and a
    hand-built payload elsewhere (the CLI's gate-error path) silently
    broke that promise until this existed."""
    return {
        "schema": SCHEMA,
        "file": file,
        # Provenance rides every payload: a host must be able to tell
        # whether two verdicts meant the same thing. `dafny_version` stays
        # None until the prover is actually reached.
        "toolchain": {
            "preamble_version": PREAMBLE_VERSION,
            "dafny_version": None,
            "taxonomy_version": TAXONOMY_VERSION,
        },
        "status": None,
        "functions": [],
        "failures": [],
        "sidecar": None,
        "stub": None,
        "artifacts_kept": keep_artifacts,
    }


def verify_structured(path: Path, outdir: Path, time_limit: int = 30,
                      hunt_counterexamples: bool = False,
                      keep_artifacts: bool = False) -> dict[str, Any]:
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

    Staging is per-call, so `outdir` must not grow without bound — the old
    shared path was at least capped by the number of distinct stems. Two
    lifetimes, each named for how it ends:

    - not kept (the default, and what an embedded backend wants): an
      ephemeral `mkdtemp`, removed in a `finally`. Unique per thread, which
      a stem- or PID-derived name is not.
    - kept: a CONTENT-ADDRESSED directory, so re-verifying the same file
      overwrites its own artifacts instead of accumulating a directory per
      run. The digest covers everything that determines the stub, so two
      calls sharing a directory agree on the final bytes — but agreeing on
      the destination is NOT the same as being safe to write concurrently,
      which is why the stub is written atomically (see
      `atomic_write_text`).

    The artifacts are purely diagnostic (nothing downstream reads the stub;
    the CLI prints its path for a human), so `payload["stub"]` is None when
    they are not kept, rather than a path that no longer exists.
    """
    payload = new_payload(str(path), keep_artifacts)
    workdir: Path | None = None
    try:
        outdir.mkdir(parents=True, exist_ok=True)
        if not keep_artifacts:
            workdir = Path(tempfile.mkdtemp(prefix="verify-", dir=outdir))
    except OSError as exc:
        payload["status"] = "tool-error"
        payload["error"] = f"cannot create work directory: {exc}"
        return payload
    try:
        # When keeping, the directory is derived later from the stub's own
        # content — it cannot be named before the stub exists.
        return _verify_into(path, outdir, workdir, payload, time_limit,
                            hunt_counterexamples, keep_artifacts)
    finally:
        if workdir is not None and not keep_artifacts:
            shutil.rmtree(workdir, ignore_errors=True)


def atomic_write_text(target: Path, text: str) -> None:
    """Write via a sibling temp file and `os.replace`.

    A plain `write_text` TRUNCATES before writing, so a concurrent reader —
    here, the Dafny process we are about to launch — can observe an empty
    or half-written file. Content-addressing makes concurrent writers agree
    on the final bytes, but agreement about the destination says nothing
    about what a reader sees mid-write. `os.replace` is atomic on POSIX, so
    a reader gets either the whole old file or the whole new one.
    """
    tmp = tempfile.NamedTemporaryFile(
        "w", dir=target.parent, prefix=target.name + ".", suffix=".tmp",
        delete=False)
    try:
        with tmp:
            tmp.write(text)
        os.replace(tmp.name, target)
    except BaseException:
        Path(tmp.name).unlink(missing_ok=True)
        raise


def stub_dir_for(outdir: Path, path: Path, stub_text: str) -> Path:
    """Content-addressed staging directory for artifacts that are KEPT.

    Stable across re-runs of an unchanged file (so nothing accumulates) and
    distinct whenever the emitted stub differs — including two same-stemmed
    modules from different directories, which is the collision that let one
    verification certify another's code.
    """
    digest = hashlib.sha256(
        (str(path.resolve()) + "\0" + stub_text).encode()
    ).hexdigest()[:12]
    return outdir / f"verify-{path.stem}-{digest}"


def _verify_into(path: Path, outdir: Path, workdir: Path | None,
                 payload: dict[str, Any], time_limit: int,
                 hunt_counterexamples: bool,
                 keep_artifacts: bool) -> dict[str, Any]:
    try:
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
    stub_text = encoded.dafny_source + sidecar.text
    try:
        if workdir is None:  # keep_artifacts: name it after its content
            workdir = stub_dir_for(outdir, path, stub_text)
            workdir.mkdir(parents=True, exist_ok=True)
        stub = workdir / f"{path.stem}.dfy"
        atomic_write_text(stub, stub_text)
    except OSError as exc:
        payload["status"] = "tool-error"
        payload["error"] = f"cannot write stub: {exc}"
        return payload
    payload["stub"] = str(stub) if keep_artifacts else None
    stub_extent = encoded.dafny_source.count("\n") + 1
    payload["toolchain"]["dafny_version"] = dafny_version()  # cached per process
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
        # `region` is NULL, not "source": nothing here attributes this
        # failure to the source rather than the sidecar, and the contract
        # tells hosts to route `unknown` by region — so a fabricated
        # attribution would send a repair agent after the wrong file, or
        # after a repair that cannot apply at all.
        payload["failures"].append({
            "kind": "unknown", "function": None, "region": None,
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
                           hunt_counterexamples: bool = False,
                           keep_artifacts: bool = False) -> list[dict[str, Any]]:
    """Same-stem inputs no longer need special handling: `verify_structured`
    stages each invocation privately, so stub paths are unique by
    construction — across calls, threads and processes, not just within
    one batch as the old `dup{n}` scheme managed."""
    return [
        verify_structured(p, outdir, time_limit=time_limit,
                          hunt_counterexamples=hunt_counterexamples,
                          keep_artifacts=keep_artifacts)
        for p in paths
    ]


def dump(payloads: list[dict[str, Any]], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payloads, indent=1))
