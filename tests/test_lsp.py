"""The LSP editor surface: JSON-RPC over pipes against the real server."""

import io
import json
from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.lsp import Server, analyze, digest, proof_view, prove

GOOD = (
    "#@ verified\n"
    "#@ ensures result == x + 1\n"
    "def bump(x: int) -> int:\n"
    "    return x + 1\n"
)

BAD = (
    "#@ ensures result >= 0\n"
    "def f(xs: list[int]) -> int:\n"
    "    return len(set(xs))\n"
)


def _frame(payload: dict) -> bytes:
    body = json.dumps(payload).encode()
    return f"Content-Length: {len(body)}\r\n\r\n".encode() + body


def _run(messages: list[dict]) -> list[dict]:
    stdin = io.BytesIO(b"".join(_frame(m) for m in messages))
    stdout = io.BytesIO()
    Server(stdin, stdout).serve()
    out, replies = stdout.getvalue(), []
    while out:
        header, _, rest = out.partition(b"\r\n\r\n")
        length = int(header.split(b":")[1])
        replies.append(json.loads(rest[:length]))
        out = rest[length:]
    return replies


def test_analyze_good_and_bad():
    diags, statuses = analyze(GOOD, "m.py")
    assert diags == []
    assert statuses == [{"name": "bump", "line": 3, "markedVerified": True,
                         "status": "conformant"}]
    diags, statuses = analyze(BAD, "m.py")
    assert len(diags) == 1
    assert diags[0]["range"]["start"]["line"] == 2  # 0-based line 3
    assert "outside the slice-1 encoder" in diags[0]["message"]
    assert statuses[0]["status"] == "nonconformant"


def test_syntax_error_is_a_diagnostic_not_a_crash():
    diags, _ = analyze("def broken(:\n", "m.py")
    assert diags and "syntax error" in diags[0]["message"]


def test_null_byte_is_a_diagnostic_not_a_dead_server():
    # SyntaxError on 3.12+, ValueError on older Pythons — either way a
    # diagnostic, never a dead server.
    diags, _ = analyze("def f():\x00\n    pass\n", "m.py")
    assert diags
    msg = diags[0]["message"]
    assert "unparseable" in msg or "null bytes" in msg


def test_tokenizer_error_is_a_diagnostic_not_a_dead_server(monkeypatch):
    # The spec-comment scan can raise TokenError on in-progress buffers
    # that ast.parse would accept; the server must publish, not die.
    import lemmapy.lsp as lsp_mod
    from tokenize import TokenError

    def boom(text, filename):
        raise TokenError("EOF in multi-line statement", (1, 0))

    monkeypatch.setattr(lsp_mod, "parse_source", boom)
    diags, statuses = analyze("x = 1\n", "m.py")
    assert diags and "unparseable" in diags[0]["message"]
    assert statuses == []


def test_module_scope_failure_is_one_diagnostic_all_nonconformant():
    # A builtin-shadowing module binding breaks the model for the whole
    # module: every function is nonconformant, but the diagnostic appears
    # exactly once, not once per function.
    src = "sum = 5\n\n" + GOOD + "\n\n" + GOOD.replace("bump", "bump2")
    diags, statuses = analyze(src, "m.py")
    shadow = [d for d in diags if "shadows a builtin" in d["message"]]
    assert len(shadow) == 1
    assert [s["status"] for s in statuses] == ["nonconformant", "nonconformant"]


def test_mixed_module_statuses_are_per_function():
    # One nonconformant function must not contaminate its neighbor.
    diags, statuses = analyze(GOOD + "\n\n" + BAD, "m.py")
    by_name = {s["name"]: s["status"] for s in statuses}
    assert by_name == {"bump": "conformant", "f": "nonconformant"}
    assert len(diags) == 1


def test_full_session_publish_and_status():
    uri = "file:///tmp/m.py"
    replies = _run([
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
        {"jsonrpc": "2.0", "method": "textDocument/didOpen",
         "params": {"textDocument": {"uri": uri, "text": BAD}}},
        {"jsonrpc": "2.0", "method": "textDocument/didChange",
         "params": {"textDocument": {"uri": uri},
                    "contentChanges": [{"text": GOOD}]}},
        {"jsonrpc": "2.0", "id": 2, "method": "lemmapy/functionStatus",
         "params": {"textDocument": {"uri": uri}}},
        {"jsonrpc": "2.0", "id": 3, "method": "shutdown", "params": {}},
        {"jsonrpc": "2.0", "method": "exit"},
    ])
    init = replies[0]
    assert init["result"]["serverInfo"]["name"] == "lemmapy-lsp"
    publishes = [r for r in replies
                 if r.get("method") == "textDocument/publishDiagnostics"]
    assert len(publishes) == 2
    assert len(publishes[0]["params"]["diagnostics"]) == 1  # BAD
    assert publishes[1]["params"]["diagnostics"] == []      # fixed by GOOD
    status = next(r for r in replies if r.get("id") == 2)
    assert status["result"]["functions"][0]["name"] == "bump"
    assert status["result"]["functions"][0]["status"] == "conformant"


def test_unknown_request_gets_method_not_found():
    replies = _run([
        {"jsonrpc": "2.0", "id": 9, "method": "textDocument/hover", "params": {}},
        {"jsonrpc": "2.0", "method": "exit"},
    ])
    assert replies[0]["error"]["code"] == -32601


def test_fixit_guidance_present_in_catchall_messages():
    # The diagnostics quality pass: catch-all rejections carry guidance.
    diags, _ = analyze(
        "#@ requires x >= 0\n"
        "#@ ensures result >= 0\n"
        "def f(x: int) -> int:\n"
        "    import os\n"
        "    return x\n",
        "m.py",
    )
    assert any("admitted:" in d["message"] for d in diags)


# -- proof status (the slow lane) --------------------------------------------

REPO = Path(__file__).resolve().parent.parent


def _proof_payload(status, functions, failures=(), error=None):
    return {"status": status, "functions": list(functions),
            "failures": list(failures), "error": error,
            "toolchain": {"preamble_version": "x", "dafny_version": "y"}}


def test_proof_view_verified_only_when_the_whole_module_is_ok():
    diags, view = proof_view(_proof_payload("ok", ["a", "b"]))
    assert diags == [] and view == {"a": "verified", "b": "verified"}


def test_unattributed_failure_never_leaves_a_peer_looking_verified():
    # `b` has no failure of its own, but a sidecar lemma did not verify --
    # every caller assumes it, so `b` is unknown, NOT verified.
    payload = _proof_payload("failed", ["a", "b"], [
        {"kind": "postcondition", "function": "a", "region": "source",
         "py_line": 4, "dafny_line": 40, "message": "might not hold"},
        {"kind": "assertion", "function": None, "region": "sidecar",
         "py_line": None, "dafny_line": 120, "message": "assertion might not hold"},
    ])
    diags, view = proof_view(payload)
    assert view == {"a": "failed", "b": "unknown"}
    assert diags[0]["range"]["start"]["line"] == 3  # 0-based, the Python line
    assert "proof: postcondition" in diags[0]["message"]
    # The sidecar obligation has no Python line: anchored at the top and
    # SAYING where it really lives, rather than pinned to unrelated code.
    assert diags[1]["range"]["start"]["line"] == 0
    assert "proof [sidecar]" in diags[1]["message"]
    assert "generated Dafny line 120" in diags[1]["message"]


def test_tool_error_claims_nothing_about_the_code():
    diags, view = proof_view(
        _proof_payload("tool-error", ["a"], error="dafny not found on PATH"))
    assert view == {"a": "unknown"}
    assert diags[0]["severity"] == 3  # information, not an error about the code
    assert "not run" in diags[0]["message"] and "dafny not found" in diags[0]["message"]


def test_proof_result_is_dropped_the_moment_the_buffer_changes():
    server = Server(io.BytesIO(), io.BytesIO())
    uri = "file:///m.py"
    server.documents[uri] = GOOD
    server.proofs[uri] = {"digest": digest(GOOD), "status": "ok",
                          "diagnostics": [_stale_diag()],
                          "functions": {"bump": "verified"}}
    assert server._proof_for(uri) is not None
    server.documents[uri] = GOOD + "\n# an edit\n"
    assert server._proof_for(uri) is None
    assert uri not in server.proofs  # discarded, not merely hidden


def _stale_diag():
    return {"range": {"start": {"line": 0, "character": 0},
                      "end": {"line": 0, "character": 1}},
            "severity": 1, "source": "lemmapy", "message": "proof: stale marker"}


def test_stale_proof_diagnostics_are_not_republished():
    replies = _run([
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
        {"jsonrpc": "2.0", "method": "textDocument/didOpen",
         "params": {"textDocument": {"uri": "file:///m.py", "text": GOOD}}},
        {"jsonrpc": "2.0", "method": "textDocument/didChange",
         "params": {"textDocument": {"uri": "file:///m.py"},
                    "contentChanges": [{"text": GOOD + "\n# edit\n"}]}},
        {"jsonrpc": "2.0", "id": 2, "method": "lemmapy/functionStatus",
         "params": {"textDocument": {"uri": "file:///m.py"}}},
        {"jsonrpc": "2.0", "method": "exit", "params": {}},
    ])
    status = [r for r in replies if r.get("id") == 2][0]["result"]
    assert status["functions"][0]["proof"] == "unknown"
    assert status["proofStatus"] is None


def test_verify_on_an_unopened_document_is_an_error_not_a_crash():
    replies = _run([
        {"jsonrpc": "2.0", "id": 1, "method": "lemmapy/verify",
         "params": {"textDocument": {"uri": "file:///nope.py"}}},
        {"jsonrpc": "2.0", "method": "exit", "params": {}},
    ])
    assert replies[0]["error"]["code"] == -32602
    assert "not open" in replies[0]["error"]["message"]


def test_verify_time_limit_is_clamped_not_trusted(monkeypatch):
    seen = {}

    def fake_prove(text, filename, time_limit=20):
        seen["limit"] = time_limit
        return _proof_payload("ok", ["bump"])

    monkeypatch.setattr("lemmapy.lsp.prove", fake_prove)
    for asked, expected in ((100000, 300), (0, 1), ("nonsense", 20)):
        _run([
            {"jsonrpc": "2.0", "method": "textDocument/didOpen",
             "params": {"textDocument": {"uri": "file:///m.py", "text": GOOD}}},
            {"jsonrpc": "2.0", "id": 1, "method": "lemmapy/verify",
             "params": {"textDocument": {"uri": "file:///m.py"},
                        "timeLimit": asked}},
            {"jsonrpc": "2.0", "method": "exit", "params": {}},
        ])
        assert seen["limit"] == expected


def test_verify_reply_and_merged_publish(monkeypatch):
    monkeypatch.setattr(
        "lemmapy.lsp.prove",
        lambda text, filename, time_limit=20: _proof_payload(
            "failed", ["bump"],
            [{"kind": "postcondition", "function": "bump", "region": "source",
              "py_line": 4, "dafny_line": 40, "message": "might not hold"}]))
    replies = _run([
        {"jsonrpc": "2.0", "method": "textDocument/didOpen",
         "params": {"textDocument": {"uri": "file:///m.py", "text": GOOD}}},
        {"jsonrpc": "2.0", "id": 7, "method": "lemmapy/verify",
         "params": {"textDocument": {"uri": "file:///m.py"}}},
        {"jsonrpc": "2.0", "method": "exit", "params": {}},
    ])
    reply = [r for r in replies if r.get("id") == 7][0]["result"]
    assert reply["status"] == "failed"
    assert reply["functions"] == [{"name": "bump", "proof": "failed"}]
    assert reply["toolchain"]["dafny_version"] == "y"
    # The worker republishes: the last publish carries the proof failure,
    # which the fast pipeline alone would never produce (GOOD is conformant).
    publishes = [r for r in replies
                 if r.get("method") == "textDocument/publishDiagnostics"]
    assert publishes[0]["params"]["diagnostics"] == []
    assert "proof: postcondition" in publishes[-1]["params"]["diagnostics"][0]["message"]


def test_shutdown_waits_for_an_in_flight_proof(monkeypatch):
    import time as _time

    def slow_prove(text, filename, time_limit=20):
        _time.sleep(0.3)
        return _proof_payload("ok", ["bump"])

    monkeypatch.setattr("lemmapy.lsp.prove", slow_prove)
    replies = _run([
        {"jsonrpc": "2.0", "method": "textDocument/didOpen",
         "params": {"textDocument": {"uri": "file:///m.py", "text": GOOD}}},
        {"jsonrpc": "2.0", "id": 9, "method": "lemmapy/verify",
         "params": {"textDocument": {"uri": "file:///m.py"}}},
        {"jsonrpc": "2.0", "method": "exit", "params": {}},
    ])
    # `exit` arrives while the prover is still running: the reply must
    # still be delivered, else the client waits forever on id 9.
    assert [r for r in replies if r.get("id") == 9]


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_prove_stages_the_on_disk_sidecar(tmp_path):
    # A buffer whose `#@ proof` clauses name sidecar lemmas must come back
    # as a PROOF result, not as `unknown lemma` manufactured by staging.
    task = REPO / "benchmark" / "tasks" / "gcd"
    src = tmp_path / "gcd.py"
    src.write_text((task / "task.py").read_text())
    (tmp_path / "gcd.proofs.dfy").write_text((task / "task.proofs.dfy").read_text())
    payload = prove(src.read_text(), str(src), time_limit=60)
    assert payload["status"] == "ok", payload
    assert payload["file"] == str(src)  # the buffer's identity, not the staging dir


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_prove_without_the_sidecar_is_a_conformance_rejection(tmp_path):
    # The control for the test above: no sidecar on disk, so the `#@ proof`
    # targets really are unknown -- and that is what comes back.
    src = tmp_path / "gcd.py"
    src.write_text((REPO / "benchmark" / "tasks" / "gcd" / "task.py").read_text())
    payload = prove(src.read_text(), str(src), time_limit=60)
    assert payload["status"] == "encode-error"
    assert "unknown lemma" in payload["failures"][0]["message"]


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_prove_reports_a_real_proof_failure(tmp_path):
    # The prover is genuinely consulted: strengthening gcd's postcondition
    # to something false must come back `failed`, attributed to the
    # function, on the Python line -- not `ok` from a short-circuit.
    task = REPO / "benchmark" / "tasks" / "gcd"
    text = task.joinpath("task.py").read_text().replace(
        "#@ ensures result >= 1", "#@ ensures result >= 2")
    src = tmp_path / "gcd.py"
    src.write_text(text)
    (tmp_path / "gcd.proofs.dfy").write_text((task / "task.proofs.dfy").read_text())
    payload = prove(text, str(src), time_limit=60)
    assert payload["status"] == "failed"
    diags, view = proof_view(payload)
    assert view == {"greatest_common_divisor": "failed"}
    assert diags and diags[0]["range"]["start"]["line"] > 0


def test_conformance_failures_are_not_reported_twice(monkeypatch):
    # A nonconformant buffer: the instant lane publishes the rejection on
    # every keystroke. The proof lane must not republish it -- one mistake,
    # one diagnostic.
    monkeypatch.setattr(
        "lemmapy.lsp.prove",
        lambda text, filename, time_limit=20: _proof_payload(
            "encode-error", ["f"],
            [{"kind": "conformance", "function": "f", "region": "source",
              "py_line": 3, "dafny_line": None,
              "message": "outside the slice-1 encoder"}]))
    replies = _run([
        {"jsonrpc": "2.0", "method": "textDocument/didOpen",
         "params": {"textDocument": {"uri": "file:///m.py", "text": BAD}}},
        {"jsonrpc": "2.0", "id": 3, "method": "lemmapy/verify",
         "params": {"textDocument": {"uri": "file:///m.py"}}},
        {"jsonrpc": "2.0", "method": "exit", "params": {}},
    ])
    publishes = [r for r in replies
                 if r.get("method") == "textDocument/publishDiagnostics"]
    assert len(publishes[0]["params"]["diagnostics"]) == 1
    assert publishes[-1]["params"]["diagnostics"] == publishes[0]["params"]["diagnostics"]
    reply = [r for r in replies if r.get("id") == 3][0]["result"]
    assert reply["functions"] == [{"name": "f", "proof": "unknown"}]


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_prove_names_the_users_sidecar_not_the_staging_copy(tmp_path):
    task = REPO / "benchmark" / "tasks" / "gcd"
    src = tmp_path / "gcd.py"
    src.write_text((task / "task.py").read_text())
    sidecar = tmp_path / "gcd.proofs.dfy"
    sidecar.write_text((task / "task.proofs.dfy").read_text())
    payload = prove(src.read_text(), str(src), time_limit=60)
    # Both paths must be openable after the call -- the staging directory
    # is gone by then.
    assert payload["sidecar"]["path"] == str(sidecar)
    assert Path(payload["file"]).exists() and Path(payload["sidecar"]["path"]).exists()
