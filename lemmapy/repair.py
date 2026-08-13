"""The proof-repair loop (M2): proofs that finish themselves.

`repair_file` drives an engine (an LLM, or a scripted stand-in for tests)
against the structured-failure interface: verify → feed the failures, the
source, and the current sidecar to the engine → the engine proposes a new
`.proofs.dfy` → the whitelist validator and the prover judge it → iterate.

The engine may edit ONLY the proof sidecar. Everything else — source,
specs, the stub — is frozen; an engine cannot weaken what it is asked to
prove. Proposals run through the same `_validate_sidecar` whitelist as
hand-written sidecars (ghost lemmas with bodies only), so a repair can
never smuggle an axiom, and a rejected proposal comes back to the engine
as the next iteration's failure payload.

All work happens on copies under the workdir; the user's sidecar is only
written (with a `.bak` of any previous content) on success with
``apply=True``.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Protocol

from .agentio import verify_structured

Engine = Callable[[dict[str, Any]], str]

RULES = """\
You are repairing a Dafny proof for a verified-Python toolchain.
You may change ONLY the proof sidecar (<stem>.proofs.dfy). Reply with the
COMPLETE new sidecar content and nothing else (no fences, no commentary).
Sidecar rules (whitelist-validated; violations are rejected):
- ghost declarations only: `lemma` / `ghost function` / `function`, each
  with a BODY (a bodiless lemma is an axiom and is rejected)
- forbidden: method, import, include, assume, axioms, attributes ({:...}),
  multiset/set/iset/map/imap, lambda arrows (=>), string @-literals
- `==>` (implication) is legal; `=>` (lambda) is not
- lemmas are invoked from Python via `#@ proof LemmaName(args)` clauses
  already present in the source; define exactly the lemmas those clauses
  name (plus any helper lemmas they call)
The preamble (PyMod, PyFloorDiv, PySlice, PySum, ...) is in scope."""


def build_request(source: str, payload: dict[str, Any],
                  attempt: int, history: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": "lemmapy-repair-request/1",
        "rules": RULES,
        "attempt": attempt,
        "source": source,
        "failures": payload,
        "sidecar": (payload.get("sidecar") or {}).get("text", ""),
        "history": history,
    }


def _render_prompt(request: dict[str, Any]) -> str:
    parts = [
        request["rules"],
        "\n## Python source (frozen)\n" + request["source"],
        "\n## Verification outcome (structured)\n"
        + json.dumps(request["failures"], indent=1),
        "\n## Current sidecar\n" + (request["sidecar"] or "(none)"),
    ]
    if request["history"]:
        parts.append("\n## Prior attempts (most recent last)\n"
                     + json.dumps(request["history"][-3:], indent=1))
    parts.append("\nReply with the complete new sidecar content only.")
    return "\n".join(parts)


def _strip_fences(text: str) -> str:
    stripped = text.strip()
    if stripped.startswith("```"):
        lines = stripped.splitlines()
        if lines[-1].strip() == "```":
            lines = lines[1:-1]
        else:
            lines = lines[1:]
        stripped = "\n".join(lines)
    return stripped.rstrip() + "\n"


def claude_engine(request: dict[str, Any]) -> str:
    """Headless `claude -p` as the default repair engine."""
    exe = shutil.which("claude")
    if exe is None:
        raise RuntimeError("engine 'claude' needs the claude CLI on PATH")
    proc = subprocess.run(
        [exe, "-p", _render_prompt(request)],
        capture_output=True, text=True, timeout=600,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"claude engine failed: {proc.stderr[:400]}")
    return _strip_fences(proc.stdout)


class _FileEngine:
    """Scripted engine: returns `1.dfy`, `2.dfy`, ... from a directory in
    attempt order. Deterministic loop testing and replay of recorded runs."""

    def __init__(self, directory: Path):
        self.directory = directory
        self.calls = 0

    def __call__(self, request: dict[str, Any]) -> str:
        self.calls += 1
        candidate = self.directory / f"{self.calls}.dfy"
        if not candidate.exists():
            raise RuntimeError(f"file engine exhausted at attempt {self.calls}")
        return candidate.read_text()


def make_engine(spec: str) -> Engine:
    if spec == "claude":
        return claude_engine
    if spec.startswith("file:"):
        return _FileEngine(Path(spec[5:]))
    raise ValueError(f"unknown engine {spec!r} (use 'claude' or 'file:<dir>')")


def _acquire_apply_lock(lock: Path):
    """Advisory flock on a persistent lock file. The kernel releases the
    lock when the holder dies, so an orphaned lock cannot block applies
    (no stale-lock reaping, hence no reap races either); the empty .lock
    file itself is inert and left in place. Returns an fd to hold, or
    None on live contention."""
    import fcntl
    import os

    fd = os.open(lock, os.O_CREAT | os.O_WRONLY)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return fd
    except OSError:
        os.close(fd)
        return None


def _apply_sidecar(user_sidecar: Path, text: str, expected_prior: str | None,
                   source_path: Path, expected_source: str) -> str:
    """Write the verified sidecar beside the source: flock-serialized,
    atomic, first-backup-wins (the earliest `.bak` is the content closest
    to the user's original), first-APPLY-wins (a concurrently applied
    proof is never overwritten), and source-guarded — the live source is
    re-checked under the lock at the last instant before the write. (An
    editor saving in the microseconds after that check is inherently
    unpreventable without cooperative source locking; the window here is
    the minimum any file-writing tool can have.)"""
    import os
    import tempfile

    lock = user_sidecar.with_name(user_sidecar.name + ".lock")
    fd = _acquire_apply_lock(lock)
    if fd is None:
        return ("verified; apply skipped: another repair is applying to "
                "this sidecar — rerun to apply")
    try:
        try:
            live = source_path.read_text()
        except OSError:
            live = None
        if live != expected_source:
            return ("verified for the source as of repair start; apply "
                    "skipped: the source changed during this repair — rerun")
        current = user_sidecar.read_text() if user_sidecar.exists() else None
        if current == text:
            return "verified (sidecar already up to date)"
        if current != expected_prior:
            return ("verified; apply skipped: the sidecar changed during "
                    "this repair (a concurrent repair applied) — rerun to "
                    "reconcile")
        if current is not None:
            bak = user_sidecar.with_name(user_sidecar.name + ".bak")
            if not bak.exists():
                bak.write_text(current)
        tmp = tempfile.NamedTemporaryFile(
            "w", dir=user_sidecar.parent, prefix=user_sidecar.name + ".",
            suffix=".tmp", delete=False)
        with tmp:
            tmp.write(text)
        os.replace(tmp.name, user_sidecar)
        return "verified (sidecar applied)"
    finally:
        os.close(fd)  # dropping the fd releases the flock


@dataclass
class RepairOutcome:
    verified: bool
    iterations: int
    reason: str
    sidecar_text: str | None = None
    history: list[dict[str, Any]] = field(default_factory=list)


def _repairable(payload: dict[str, Any]) -> bool:
    """A proof edit can help with failed proofs and sidecar-validation
    rejections — not with spec errors or source-conformance rejections."""
    if payload["status"] == "failed":
        return True
    if payload["status"] == "encode-error":
        return any("proof sidecar" in (f.get("message") or "")
                   or "proof clause" in (f.get("message") or "")
                   for f in payload["failures"])
    return False


def repair_file(path: Path, outdir: Path, engine: Engine,
                max_iterations: int = 4, time_limit: int = 30,
                apply: bool = False) -> RepairOutcome:
    outdir.mkdir(parents=True, exist_ok=True)
    # A fresh private work directory per invocation: two overlapping
    # repairs of same-named sources sharing an outdir must never verify
    # (or apply) each other's files.
    work = Path(tempfile.mkdtemp(prefix="work-", dir=outdir))
    work_src = work / path.name
    work_src.write_text(path.read_text())
    user_sidecar = path.with_name(path.stem + ".proofs.dfy")
    initial_sidecar = user_sidecar.read_text() if user_sidecar.exists() else None
    work_sidecar = work / f"{path.stem}.proofs.dfy"
    if user_sidecar.exists():
        work_sidecar.write_text(user_sidecar.read_text())
    else:
        # A reused workdir may hold a previous run's sidecar; verifying
        # against it would fake iteration-zero success (and --apply would
        # write stale proof content beside the source).
        work_sidecar.unlink(missing_ok=True)
    source = work_src.read_text()
    history: list[dict[str, Any]] = []

    for attempt in range(max_iterations + 1):
        payload = verify_structured(work_src, work / f"iter{attempt}",
                                    time_limit=time_limit)
        if payload["status"] == "ok":
            text = work_sidecar.read_text() if work_sidecar.exists() else None
            if apply and text is not None:
                reason = _apply_sidecar(user_sidecar, text, initial_sidecar,
                                        path, source)
                return RepairOutcome(True, attempt, reason, text, history)
            return RepairOutcome(True, attempt, "verified", text, history)
        if not _repairable(payload):
            return RepairOutcome(False, attempt,
                                 f"not repairable by proof edits: "
                                 f"{payload['status']}", None, history)
        if attempt == max_iterations:
            break
        request = build_request(source, payload, attempt, history)
        try:
            proposal = _strip_fences(engine(request))
        except Exception as exc:
            return RepairOutcome(False, attempt, f"engine error: {exc}",
                                 None, history)
        work_sidecar.write_text(proposal)
        history.append({
            "attempt": attempt,
            "failures": payload["failures"],
            "proposal": proposal,
        })
    return RepairOutcome(False, max_iterations, "iteration budget exhausted",
                         None, history)
