"""A minimal, dependency-free LSP server (M2 editor surface).

`lemmapy lsp` speaks Language Server Protocol over stdio and publishes
line-precise diagnostics on open/change/save from the fast pipeline
(spec parse + the fragment-conformance encoder dry-run — no Dafny, no
basedpyright, so feedback is instant). Per-function status is served via
the custom request `lemmapy/functionStatus`, suitable for code lenses:
`conformant` / `nonconformant` per spec'd function, with the `#@ verified`
marker echoed so a client can distinguish intent from state.

Deliberately v0: proof status (Dafny) and the type gate are batch tools
(`lemmapy verify --report`); wiring their results into the server is
future work, noted in ROADMAP.
"""

from __future__ import annotations

import json
import sys
from tokenize import TokenError
from typing import Any, BinaryIO
from urllib.parse import unquote, urlparse

from .backends.dafny.encoder import EncodeError, encode_module
from .frontend.extract import parse_source
from .frontend.parse import ModuleSpecs


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


class Server:
    def __init__(self, reader: BinaryIO, writer: BinaryIO):
        self.reader = reader
        self.writer = writer
        self.documents: dict[str, str] = {}
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
        self.writer.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii"))
        self.writer.write(body)
        self.writer.flush()

    def _reply(self, msg_id: Any, result: Any) -> None:
        self._send({"jsonrpc": "2.0", "id": msg_id, "result": result})

    def _notify(self, method: str, params: dict[str, Any]) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    # -- document pipeline ----------------------------------------------------

    def _publish(self, uri: str) -> None:
        text = self.documents.get(uri, "")
        filename = unquote(urlparse(uri).path) or uri
        diagnostics, _ = analyze(text, filename)
        self._notify("textDocument/publishDiagnostics",
                     {"uri": uri, "diagnostics": diagnostics})

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
            self.documents.pop(params["textDocument"]["uri"], None)
        elif method == "lemmapy/functionStatus":
            uri = params["textDocument"]["uri"]
            text = self.documents.get(uri, "")
            filename = unquote(urlparse(uri).path) or uri
            _, statuses = analyze(text, filename)
            self._reply(msg_id, {"functions": statuses})
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


def main() -> int:
    Server(sys.stdin.buffer, sys.stdout.buffer).serve()
    return 0
