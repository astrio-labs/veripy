"""The LSP editor surface: JSON-RPC over pipes against the real server."""

import io
import json

from lemmapy.lsp import Server, analyze

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
