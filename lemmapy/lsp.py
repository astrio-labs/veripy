"""A minimal, dependency-free LSP server (M2 editor surface).

`lemmapy lsp` speaks Language Server Protocol over stdio at two speeds,
because the two kinds of feedback have wildly different costs:

- **instant, automatic** — line-precise diagnostics on open/change/save
  from the fast pipeline (spec parse + the fragment-conformance encoder
  dry-run; no Dafny, no basedpyright), plus per-function conformance via
  the custom request `lemmapy/functionStatus`.
- **slow, explicit** — proof status from the real prover, via the custom
  request `lemmapy/verify`. Never on the keystroke path: a client binds it
  to a command or a save hook. It runs on a worker thread so the server
  keeps answering while Dafny thinks, and its diagnostics are merged into
  subsequent publishes.

Proof results are pinned to the exact buffer that produced them (SHA-256
of the text). The moment the buffer changes they are DROPPED rather than
re-anchored: a proof diagnostic reported against a line the user has since
edited is worse than no diagnostic, and `functionStatus` says `unknown`
rather than repeating a verdict the code no longer supports.

For the same reason the newest request for a document always wins: an
older `lemmapy/verify` still in flight is superseded — answered with
ContentModified, never allowed to write the cache — however long it takes
to come back.

The type gate (basedpyright) remains a batch tool.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import sys
import tempfile
import threading
import time
from pathlib import Path
from tokenize import TokenError
from typing import Any, BinaryIO
from urllib.parse import unquote, urlparse

from .backends.dafny.encoder import EncodeError, encode_module
from .frontend.extract import parse_source
from .frontend.parse import ModuleSpecs


# TOTAL time shutdown waits for in-flight proofs to answer, shared across
# all of them -- per-worker it would multiply by however many a client
# happened to fire. Bounded either way: `exit` must not be hostage to a
# slow prover.
_SHUTDOWN_JOIN_S = 60.0

# How many Dafny processes the slow lane may have running at once. Nothing
# upstream throttles: a save hook or a held-down keybinding can fire
# `lemmapy/verify` far faster than the prover answers, and each request used
# to mean another external process. One at a time, with the rest queued
# behind it (and superseded requests dropped at the gate, see
# `_prove_and_reply`), makes the editor's load on the machine a constant.
_MAX_PROVERS = 1

# LSP's ContentModified. Not an error in the user's code and not a verdict:
# the request was overtaken by a newer one for the same document.
_CONTENT_MODIFIED = -32801


def _diagnostic(line: int, message: str, severity: int = 1) -> dict[str, Any]:
    zero = max(0, (line or 1) - 1)
    return {
        "range": {
            "start": {"line": zero, "character": 0},
            "end": {"line": zero, "character": 1000},
        },
        "severity": severity,
        "source": "lemmapy",
        "message": message,
    }


def analyze(text: str, filename: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """(diagnostics, function statuses) from the fast pipeline. Conformance
    is judged PER FUNCTION (each spec'd function is encoded on its own), so
    one nonconformant function never contaminates its neighbors' status."""
    diagnostics: list[dict[str, Any]] = []
    statuses: list[dict[str, Any]] = []
    try:
        specs = parse_source(text, filename=filename)
    except SyntaxError as exc:
        diagnostics.append(_diagnostic(exc.lineno or 1, f"syntax error: {exc.msg}"))
        return diagnostics, statuses
    except (ValueError, TokenError) as exc:
        # Null characters (ValueError on older Pythons) or a spec-comment
        # tokenizer failure on an in-progress buffer -- a diagnostic,
        # never a dead server.
        diagnostics.append(_diagnostic(1, f"unparseable buffer: {exc}"))
        return diagnostics, statuses
    for clause in [*specs.errors, *specs.orphans]:
        if clause.error:
            diagnostics.append(_diagnostic(clause.line, f"spec: {clause.error}"))
    # Module-scope validation (builtin-shadow scan, duplicate defs) runs
    # ONCE via an empty-specs encode: one diagnostic, and every function is
    # honestly nonconformant -- without repeating the message per function.
    module_error = False
    try:
        encode_module(text, ModuleSpecs(functions=[], orphans=[]),
                      module_name=filename)
    except EncodeError as exc:
        module_error = True
        diagnostics.append(_diagnostic(exc.line or 1, f"fragment: {exc.message}"))
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        module_error = True
        diagnostics.append(_diagnostic(1, f"fragment: {exc}"))
    for fn in specs.functions:
        broken = module_error or any(c.error for c in fn.clauses)
        if not broken:
            try:
                # Sidecar-less on purpose: the LSP sees buffers, not files;
                # unknown `#@ proof` targets surface as diagnostics.
                encode_module(text, ModuleSpecs(functions=[fn], orphans=[]),
                              module_name=filename)
            except EncodeError as exc:
                broken = True
                diagnostics.append(_diagnostic(
                    exc.line or fn.lineno, f"fragment: {exc.message}"))
            except (OSError, UnicodeDecodeError, ValueError) as exc:
                broken = True
                diagnostics.append(_diagnostic(fn.lineno, f"fragment: {exc}"))
        statuses.append({
            "name": fn.name,
            "line": fn.lineno,
            "markedVerified": fn.verified,
            "status": "nonconformant" if broken else "conformant",
        })
    return diagnostics, statuses


def digest(text: str) -> str:
    """The identity a proof result is pinned to."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def prove(text: str, filename: str, time_limit: int = 20) -> dict[str, Any]:
    """Run the real prover over a BUFFER; return the structured payload.

    The buffer is staged into a private temp directory under the module's
    own stem, and the on-disk proof sidecar — when the buffer corresponds
    to a real file with a `<stem>.proofs.dfy` next to it — is staged
    alongside it. Without that copy every `#@ proof` clause would come
    back as `unknown lemma`, i.e. a conformance rejection manufactured by
    the staging rather than a fact about the user's code.

    Never raises: `verify_structured` turns every expected failure — no
    prover on PATH included — into a payload, and the one failure that
    happens before it is reached (a sidecar that cannot be copied) is
    turned into one here.
    """
    from .agentio import new_payload, verify_structured

    stem = Path(filename).stem or "buffer"
    work = Path(tempfile.mkdtemp(prefix="lsp-prove-"))
    try:
        staged = work / f"{stem}.py"
        staged.write_text(text)
        origin = Path(filename)
        sidecar = origin.with_name(origin.stem + ".proofs.dfy")
        try:
            if sidecar.is_file():
                shutil.copyfile(sidecar, staged.with_name(f"{stem}.proofs.dfy"))
        except OSError as exc:
            # A sidecar that is there but cannot be copied is an ENVIRONMENT
            # failure, and it must be said as one. Carrying on would verify
            # the buffer against an empty lemma set, so every valid `#@
            # proof` clause would come back `unknown lemma` — the staging
            # manufacturing a conformance rejection against the user's
            # source, which is the exact thing staging the sidecar exists to
            # prevent. `verify_structured` cannot catch this for us: it only
            # ever sees the staging directory, where the sidecar is simply
            # absent.
            payload = new_payload(filename)
            payload["status"] = "tool-error"
            payload["error"] = f"unreadable proof sidecar {sidecar}: {exc}"
            return payload
        payload = verify_structured(staged, work / "out", time_limit=time_limit)
        # Re-point provenance at the user's world. The staging directory is
        # about to be deleted, so reporting paths inside it would hand a
        # client two filenames it can never open.
        payload["file"] = filename
        if payload.get("sidecar"):
            payload["sidecar"]["path"] = str(sidecar)
        return payload
    finally:
        shutil.rmtree(work, ignore_errors=True)


def proof_view(payload: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """(diagnostics, per-function proof status) from a structured payload.

    Status is deliberately three-valued, and `verified` is only ever
    reached through a wholly `ok` module. A function with no failure
    attributed to it is `unknown`, NOT `verified`: a failing sidecar lemma
    is assumed by every caller, and a function that calls a peer whose
    postcondition failed is correct only modulo a contract nothing
    discharges. Both would read as a green check beside code that has not
    been proven.
    """
    status = payload.get("status")
    functions: list[str] = list(payload.get("functions") or [])
    failures: list[dict[str, Any]] = list(payload.get("failures") or [])
    diagnostics: list[dict[str, Any]] = []

    if status == "ok":
        return diagnostics, dict.fromkeys(functions, "verified")
    if status in ("spec-error", "encode-error"):
        # The instant lane already published these, line-precise, on the
        # last keystroke -- and its sidecar-less encode reports a superset
        # (adding known lemmas only removes errors). Re-emitting them here
        # would show every conformance rejection twice.
        return diagnostics, dict.fromkeys(functions, "unknown")
    if status == "tool-error":
        # Not a verdict about the code (no prover, unreadable sidecar, a
        # crash): one informational diagnostic, and nothing is claimed.
        diagnostics.append(_diagnostic(1, f"proof: not run — {payload.get('error')}",
                                       severity=3))
        return diagnostics, dict.fromkeys(functions, "unknown")

    view = dict.fromkeys(functions, "unknown")
    for rec in failures:
        kind = rec.get("kind") or "failure"
        name = rec.get("function")
        if name in view:
            view[name] = "failed"
        if rec.get("py_line"):
            diagnostics.append(_diagnostic(
                rec["py_line"], f"proof: {kind} — {rec.get('message')}"))
        else:
            # No Python line: the obligation lives in the sidecar (or
            # nowhere). Anchor it at the top of the buffer and SAY where it
            # really is, rather than pinning it to an unrelated line.
            where = rec.get("region") or "module"
            at = rec.get("dafny_line")
            suffix = f" (generated Dafny line {at})" if at else ""
            diagnostics.append(_diagnostic(
                1, f"proof [{where}]: {kind} — {rec.get('message')}{suffix}"))
    return diagnostics, view


class Server:
    def __init__(self, reader: BinaryIO, writer: BinaryIO):
        self.reader = reader
        self.writer = writer
        self.documents: dict[str, str] = {}
        # uri -> {"digest", "diagnostics", "functions", "status"}. Kept only
        # while the buffer still hashes to `digest` (see `_proof_for`).
        self.proofs: dict[str, dict[str, Any]] = {}
        self._write = threading.Lock()  # workers and the read loop both send
        self._workers: list[threading.Thread] = []
        # Proofs finish out of order: a worker started EARLIER can finish
        # LATER (a longer buffer, a timeout, a queue). `_latest[uri]` is the
        # sequence number of the newest `lemmapy/verify` for that document,
        # so the cache is decided by REQUEST order and a superseded worker
        # writes nothing. Completion order would let a stale timeout or
        # tool-error replace a newer success, and — because a result for
        # different text is then discarded as stale — silently erase the
        # current buffer's verdict and its diagnostics.
        self._state = threading.Lock()  # guards proofs, _latest, _seq
        self._seq = 0
        self._latest: dict[str, int] = {}
        self._provers = threading.Semaphore(_MAX_PROVERS)
        self.running = True

    # -- wire format ----------------------------------------------------------

    def _read_message(self) -> dict[str, Any] | None:
        headers: dict[str, str] = {}
        while True:
            line = self.reader.readline()
            if not line:
                return None
            stripped = line.decode("ascii", "replace").strip()
            if not stripped:
                break
            key, _, value = stripped.partition(":")
            headers[key.strip().lower()] = value.strip()
        length = int(headers.get("content-length", "0"))
        if length <= 0:
            return None
        return json.loads(self.reader.read(length).decode("utf-8"))

    def _send(self, payload: dict[str, Any]) -> None:
        body = json.dumps(payload).encode("utf-8")
        # A proof worker and the read loop can both reach this; without the
        # lock two messages interleave mid-frame and the client's parser
        # desynchronises for the rest of the session.
        with self._write:
            self.writer.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii"))
            self.writer.write(body)
            self.writer.flush()

    def _reply(self, msg_id: Any, result: Any) -> None:
        self._send({"jsonrpc": "2.0", "id": msg_id, "result": result})

    def _notify(self, method: str, params: dict[str, Any]) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    # -- document pipeline ----------------------------------------------------

    def _proof_for(self, uri: str) -> dict[str, Any] | None:
        """The cached proof result IF it still describes this buffer.

        A mismatch is not a soft "stale" flag — the entry is discarded, so
        an editor that never re-verifies cannot keep showing a verdict for
        code the user has since rewritten.
        """
        current = digest(self.documents.get(uri, ""))
        with self._state:
            cached = self.proofs.get(uri)
            if cached is None:
                return None
            if cached["digest"] != current:
                self.proofs.pop(uri, None)
                return None
            return cached

    def _claim(self, uri: str) -> int:
        """Register a new proof request for `uri` and supersede its
        predecessors. Sequence numbers are global and never reused, so a
        worker for a document that was closed and reopened cannot be
        mistaken for a current one."""
        with self._state:
            self._seq += 1
            self._latest[uri] = self._seq
            return self._seq

    def _superseded(self, uri: str, seq: int) -> bool:
        with self._state:
            return self._latest.get(uri) != seq

    def _content_modified(self, msg_id: Any, uri: str) -> None:
        # Answered, not dropped: a client blocked on an id nobody ever
        # replies to waits forever.
        self._send({"jsonrpc": "2.0", "id": msg_id,
                    "error": {"code": _CONTENT_MODIFIED,
                              "message": "superseded by a newer "
                                         f"lemmapy/verify for {uri}"}})

    def _publish(self, uri: str) -> None:
        text = self.documents.get(uri, "")
        filename = unquote(urlparse(uri).path) or uri
        diagnostics, _ = analyze(text, filename)
        cached = self._proof_for(uri)
        if cached is not None:
            diagnostics = [*diagnostics, *cached["diagnostics"]]
        self._notify("textDocument/publishDiagnostics",
                     {"uri": uri, "diagnostics": diagnostics})

    def _prove_and_reply(self, msg_id: Any, uri: str, text: str,
                         filename: str, time_limit: int, seq: int) -> None:
        """Worker body: prove the SNAPSHOT taken when the request arrived."""
        with self._provers:
            # Re-checked here, holding a prover slot: a burst on one
            # document queues up behind the running proof and then collapses
            # — everything but the newest request leaves without ever
            # starting Dafny.
            if self._superseded(uri, seq):
                self._content_modified(msg_id, uri)
                return
            payload = prove(text, filename, time_limit=time_limit)
        diagnostics, view = proof_view(payload)
        with self._state:
            if self._latest.get(uri) != seq:
                # Overtaken while the prover ran. The verdict is real but it
                # describes a snapshot the client has moved past, so it is
                # neither cached nor reported as this document's status.
                stale = True
            else:
                self.proofs[uri] = {  # one atomic rebind; no partial state
                    "digest": digest(text),
                    "diagnostics": diagnostics,
                    "functions": view,
                    "status": payload.get("status"),
                }
                stale = False
        if stale:
            self._content_modified(msg_id, uri)
            return
        self._reply(msg_id, {
            "status": payload.get("status"),
            "toolchain": payload.get("toolchain"),
            "functions": [{"name": n, "proof": p} for n, p in view.items()],
            "diagnostics": diagnostics,
            "error": payload.get("error"),
        })
        self._publish(uri)

    # -- dispatch -------------------------------------------------------------

    def handle(self, msg: dict[str, Any]) -> None:
        method = msg.get("method", "")
        params = msg.get("params", {}) or {}
        msg_id = msg.get("id")
        if method == "initialize":
            self._reply(msg_id, {
                "capabilities": {
                    "textDocumentSync": {"openClose": True, "change": 1, "save": True},
                },
                "serverInfo": {"name": "lemmapy-lsp"},
            })
        elif method == "shutdown":
            self._reply(msg_id, None)
        elif method == "exit":
            self.running = False
        elif method == "textDocument/didOpen":
            doc = params["textDocument"]
            self.documents[doc["uri"]] = doc["text"]
            self._publish(doc["uri"])
        elif method == "textDocument/didChange":
            uri = params["textDocument"]["uri"]
            changes = params.get("contentChanges") or []
            if changes:
                self.documents[uri] = changes[-1]["text"]  # full sync
            self._publish(uri)
        elif method == "textDocument/didSave":
            self._publish(params["textDocument"]["uri"])
        elif method == "textDocument/didClose":
            uri = params["textDocument"]["uri"]
            self.documents.pop(uri, None)
            with self._state:
                self.proofs.pop(uri, None)
                # Also supersedes anything still in flight for it: a proof
                # that lands after the close must not resurrect the entry.
                self._latest.pop(uri, None)
        elif method == "lemmapy/functionStatus":
            uri = params["textDocument"]["uri"]
            text = self.documents.get(uri, "")
            filename = unquote(urlparse(uri).path) or uri
            _, statuses = analyze(text, filename)
            cached = self._proof_for(uri)
            proofs = cached["functions"] if cached else {}
            for entry in statuses:
                # `unknown` covers both "never proved" and "proved, then
                # edited" — from a lens's point of view they are the same
                # thing: nothing currently backs a claim about this code.
                entry["proof"] = proofs.get(entry["name"], "unknown")
            self._reply(msg_id, {"functions": statuses,
                                 "proofStatus": cached["status"] if cached else None})
        elif method == "lemmapy/verify":
            uri = params["textDocument"]["uri"]
            if uri not in self.documents:
                self._send({"jsonrpc": "2.0", "id": msg_id,
                            "error": {"code": -32602,
                                      "message": f"document not open: {uri}"}})
                return
            # Clamped, not trusted: a client typo of 100000 would park a
            # Dafny process for the rest of the session.
            try:
                limit = int(params.get("timeLimit", 20))
            except (TypeError, ValueError):
                limit = 20
            limit = max(1, min(limit, 300))
            # The buffer is SNAPSHOT here. The user keeps typing while the
            # prover runs; the result is pinned to what was actually proved.
            text = self.documents[uri]
            filename = unquote(urlparse(uri).path) or uri
            seq = self._claim(uri)
            worker = threading.Thread(
                target=self._prove_and_reply,
                args=(msg_id, uri, text, filename, limit, seq), daemon=True)
            self._workers = [w for w in self._workers if w.is_alive()]
            self._workers.append(worker)
            worker.start()
        elif msg_id is not None:
            # Unknown request: honest MethodNotFound instead of silence.
            self._send({"jsonrpc": "2.0", "id": msg_id,
                        "error": {"code": -32601, "message": f"unknown method {method}"}})

    def serve(self) -> None:
        while self.running:
            msg = self._read_message()
            if msg is None:
                break
            self.handle(msg)
        # Exiting with a proof in flight would drop its reply and leave the
        # client waiting on an id that can never be answered.
        deadline = time.monotonic() + _SHUTDOWN_JOIN_S
        for worker in self._workers:
            worker.join(timeout=max(0.0, deadline - time.monotonic()))


def main() -> int:
    Server(sys.stdin.buffer, sys.stdout.buffer).serve()
    return 0
