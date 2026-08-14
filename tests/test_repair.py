"""The proof-repair loop, driven by the scripted file engine — verifies the
loop mechanics (feedback, validation, apply) without an LLM."""

from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.cli import main
from lemmapy.repair import (
    RULES,
    _strip_fences,
    build_request,
    make_engine,
    repair_file,
)

# A task whose `#@ proof` clause names a lemma only the sidecar can supply:
# without it, encode fails (repairable); with a bodiless one, the whitelist
# rejects it (axiom); with the real one, it verifies.
NEEDS_LEMMA = (
    "#@ ensures result == x\n"
    "def f(x: int) -> int:\n"
    "    #@ proof Obvious(x)\n"
    "    y = x\n"
    "    return y\n"
)

BODILESS = "lemma Obvious(x: int)\n  ensures x == x\n"
GOOD = "lemma Obvious(x: int)\n  ensures x == x\n{\n}\n"


def test_claude_engine_denies_tools():
    # Measurement integrity: with tools on, a headless agent once FOUND the
    # golden sidecar in the repo and returned it verbatim. The command must
    # deny all tools.
    from lemmapy.repair import _claude_cmd

    cmd = _claude_cmd("/usr/bin/claude", "prompt text")
    assert "--disallowedTools" in cmd
    assert cmd[cmd.index("--disallowedTools") + 1] == "*"
    # Ordering is load-bearing: --disallowedTools is variadic and would
    # swallow a prompt placed after it as tool-name rules.
    assert cmd.index("prompt text") < cmd.index("--disallowedTools")


def test_claude_cmd_model_and_json_keep_denial_last():
    # The engine-matrix additions (--model, --output-format json) must not
    # reshape the pinned invariant: `--disallowedTools "*"` stays the FINAL
    # two argv entries, the prompt stays before it.
    from lemmapy.repair import _claude_cmd

    cmd = _claude_cmd("/usr/bin/claude", "prompt text", model="opus",
                      json_output=True)
    assert cmd[-2:] == ["--disallowedTools", "*"]
    assert cmd.index("prompt text") < cmd.index("--disallowedTools")
    i = cmd.index("--model")
    assert cmd[i + 1] == "opus"
    j = cmd.index("--output-format")
    assert cmd[j + 1] == "json"


def test_claude_engine_runs_in_empty_sandbox(monkeypatch):
    # The other half of measurement integrity: the subprocess must run in
    # an isolated EMPTY directory, not the repository (where a tool-bearing
    # or path-guessing engine once found the golden sidecar).
    import lemmapy.repair as repair_mod

    seen = {}

    def fake_run(cmd, **kwargs):
        import os

        seen["cwd"] = kwargs.get("cwd")
        seen["entries"] = os.listdir(kwargs["cwd"])

        class Proc:
            returncode = 0
            stdout = "lemma L()\n{\n}\n"
            stderr = ""

        return Proc()

    monkeypatch.setattr(repair_mod.subprocess, "run", fake_run)
    monkeypatch.setattr(repair_mod.shutil, "which", lambda name: "/fake/claude")
    request = {"rules": "r", "attempt": 0, "source": "s",
               "failures": {}, "sidecar": "", "history": []}
    out = repair_mod.claude_engine(request)
    assert out == "lemma L()\n{\n}\n"
    assert seen["cwd"] is not None
    assert Path(seen["cwd"]).name.startswith("lemmapy-engine-")
    assert seen["entries"] == []  # nothing to find in the sandbox
    assert Path(seen["cwd"]).resolve() != Path.cwd().resolve()


def test_make_engine_specs():
    assert callable(make_engine("claude"))
    assert callable(make_engine("file:/tmp/x"))
    with pytest.raises(ValueError, match="unknown engine"):
        make_engine("gpt")


def test_make_engine_model_specs():
    from lemmapy.repair import _ApiEngine, _ClaudeEngine

    engine = make_engine("claude:opus")
    assert isinstance(engine, _ClaudeEngine) and engine.model == "opus"
    assert make_engine("claude").model is None
    # argv hygiene: empty or flag-shaped "models" must not reach the CLI.
    with pytest.raises(ValueError, match="unknown engine"):
        make_engine("claude:")
    with pytest.raises(ValueError, match="unknown engine"):
        make_engine("claude:-x")
    api = make_engine("api:openrouter/moonshotai/kimi-k3")
    assert isinstance(api, _ApiEngine)
    assert api.provider == "openrouter"
    assert api.model == "moonshotai/kimi-k3"  # model may itself contain '/'
    with pytest.raises(ValueError, match="unknown engine"):
        make_engine("api:no-slash")
    with pytest.raises(ValueError, match="unknown api provider"):
        make_engine("api:nonesuch/model")


# Field names pinned from a live `claude -p --output-format json` run
# (CLI 2.1.193), trimmed to the fields the parser reads.
CLAUDE_JSON_SAMPLE = (
    '{"type":"result","subtype":"success","is_error":false,'
    '"duration_api_ms":2040,"num_turns":1,"result":"lemma L()\\n{\\n}",'
    '"total_cost_usd":0.0274,'
    '"usage":{"input_tokens":2,"cache_creation_input_tokens":2681,'
    '"cache_read_input_tokens":0,"output_tokens":4},'
    '"modelUsage":{"claude-opus-4-8[1m]":{"inputTokens":2}}}'
)


def test_parse_claude_json():
    from lemmapy.repair import _parse_claude_json

    text, usage = _parse_claude_json(CLAUDE_JSON_SAMPLE)
    assert text == "lemma L()\n{\n}"
    assert usage["input_tokens"] == 2
    assert usage["output_tokens"] == 4
    assert usage["cache_creation_input_tokens"] == 2681
    assert usage["cost_usd"] == 0.0274
    assert usage["models"] == ["claude-opus-4-8[1m]"]
    # Missing fields degrade to None, not KeyError.
    text, usage = _parse_claude_json('{"result":"x"}')
    assert text == "x" and usage["input_tokens"] is None
    # is_error surfaces as an engine failure.
    with pytest.raises(RuntimeError, match="claude engine error"):
        _parse_claude_json('{"is_error":true,"result":"boom"}')
    # Non-JSON stdout (format drift) degrades to text mode.
    assert _parse_claude_json("plain text") == ("plain text", None)


def test_claude_engine_records_usage(monkeypatch):
    import lemmapy.repair as repair_mod
    from lemmapy.repair import _ClaudeEngine

    seen = {}

    def fake_run(cmd, **kwargs):
        import os

        seen["cmd"] = cmd
        seen["entries"] = os.listdir(kwargs["cwd"])

        class Proc:
            returncode = 0
            stdout = CLAUDE_JSON_SAMPLE
            stderr = ""

        return Proc()

    monkeypatch.setattr(repair_mod.subprocess, "run", fake_run)
    monkeypatch.setattr(repair_mod.shutil, "which", lambda name: "/fake/claude")
    engine = _ClaudeEngine(model="opus")
    request = {"rules": "r", "attempt": 0, "source": "s",
               "failures": {}, "sidecar": "", "history": []}
    assert engine(request) == "lemma L()\n{\n}\n"
    assert engine.usage_log[-1]["output_tokens"] == 4
    assert engine.usage_log[-1]["models"] == ["claude-opus-4-8[1m]"]
    # The sandbox and the pinned command shape survive the JSON path.
    assert seen["entries"] == []
    assert seen["cmd"][-2:] == ["--disallowedTools", "*"]
    assert "opus" in seen["cmd"]


def test_api_engine_parses_completion_and_usage(monkeypatch):
    import io
    import urllib.request

    seen = {}

    class FakeResp(io.BytesIO):
        def __enter__(self):
            return self

        def __exit__(self, *exc):
            return False

    def fake_urlopen(req, timeout=None):
        import json as _json

        seen["url"] = req.full_url
        seen["auth"] = req.headers.get("Authorization")
        seen["body"] = _json.loads(req.data.decode())
        return FakeResp(_json.dumps({
            "model": "moonshotai/kimi-k3-0811",
            "choices": [{"message": {"content": "```dafny\nlemma L()\n{\n}\n```"}}],
            "usage": {"prompt_tokens": 100, "completion_tokens": 7},
        }).encode())

    monkeypatch.setattr(urllib.request, "urlopen", fake_urlopen)
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-test")
    engine = make_engine("api:openrouter/moonshotai/kimi-k3")
    request = {"rules": "r", "attempt": 0, "source": "s",
               "failures": {}, "sidecar": "", "history": []}
    assert engine(request) == "lemma L()\n{\n}\n"  # fences stripped
    assert seen["url"].endswith("/chat/completions")
    assert seen["auth"] == "Bearer sk-test"
    assert seen["body"]["model"] == "moonshotai/kimi-k3"
    assert engine.usage_log[-1]["input_tokens"] == 100
    assert engine.usage_log[-1]["models"] == ["moonshotai/kimi-k3-0811"]


def test_api_engine_requires_key(monkeypatch):
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    engine = make_engine("api:openai/gpt-5.6-terra")
    with pytest.raises(RuntimeError, match="OPENAI_API_KEY"):
        engine({"rules": "r", "attempt": 0, "source": "s",
                "failures": {}, "sidecar": "", "history": []})


def test_strip_fences():
    fenced = "```dafny\nlemma L()\n{\n}\n```"
    assert _strip_fences(fenced) == "lemma L()\n{\n}\n"
    assert _strip_fences("lemma L()\n{\n}\n") == "lemma L()\n{\n}\n"


def test_request_carries_rules_and_history():
    payload = {"status": "failed", "failures": [], "sidecar": {"text": "s"}}
    req = build_request("src", payload, 2, [{"attempt": 1}])
    assert req["rules"] == RULES
    assert req["sidecar"] == "s"
    assert req["attempt"] == 2


def test_render_prompt_serves_every_exam_schema():
    # ONE renderer must serve every exam: engines are shared, and a request
    # shape the renderer cannot handle raises inside the engine, scoring the
    # whole cell as an engine error. (This is exactly how the spec-writing
    # exam first failed: KeyError 'failures' on every task.)
    from lemmapy.benchmark.specexam import build_spec_request
    from lemmapy.repair import _render_prompt

    repair_req = build_request(
        "SRC", {"status": "failed", "failures": [{"kind": "postcondition"}],
                "sidecar": {"text": "lemma L() {}"}}, 0, [])
    text = _render_prompt(repair_req)
    assert "SRC" in text and "postcondition" in text
    assert text.rstrip().endswith("sidecar content only.")

    spec_req = build_spec_request(
        "SRC", "mini", 1,
        [{"kind": "freeze", "line": 3, "message": "changed"}],
        [{"attempt": 0, "errors": ["freeze"]}])
    text = _render_prompt(spec_req)
    assert "SRC" in text and "freeze" in text
    assert "Verification outcome" not in text  # no such section here
    assert "Current sidecar" not in text
    assert text.rstrip().endswith("annotated file only.")

    # An empty feedback list renders no feedback section at all.
    first = _render_prompt(build_spec_request("SRC", "mini", 0, [], []))
    assert "rejected as malformed" not in first


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_loop_recovers_from_rejected_proposal_then_verifies(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(BODILESS)  # rejected: axiom
    (attempts / "2.dfy").write_text(GOOD)      # accepted, verifies
    engine = make_engine(f"file:{attempts}")
    outcome = repair_file(src, tmp_path / "out", engine, max_iterations=4)
    assert outcome.verified
    assert outcome.iterations == 2
    # The rejected attempt is in the history the engine saw.
    assert any("axiom" in str(h["failures"]) for h in outcome.history[1:])
    # apply=False: the user's tree is untouched.
    assert not (tmp_path / "m.proofs.dfy").exists()


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_apply_writes_sidecar_and_cli_reports(tmp_path, capsys):
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(GOOD)
    status = main(["repair", str(src), "-o", str(tmp_path / "out"),
                   "--engine", f"file:{attempts}", "--apply"])
    assert status == 0
    assert "VERIFIED after 1 repair iteration(s)" in capsys.readouterr().out
    assert (tmp_path / "m.proofs.dfy").read_text() == GOOD
    # Re-running now verifies on iteration 0 without consulting the engine.
    exhausted = make_engine(f"file:{tmp_path / 'empty'}")
    outcome = repair_file(src, tmp_path / "out2", exhausted)
    assert outcome.verified and outcome.iterations == 0


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_apply_is_lock_serialized_and_backup_preserves_first(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(GOOD)
    sidecar = tmp_path / "m.proofs.dfy"
    lock = tmp_path / "m.proofs.dfy.lock"

    # Contention: a HELD flock means nothing is written, with a clear
    # reason. (A leftover lock file with no holder is inert — see
    # test_orphaned_lock_file_is_inert_held_flock_blocks.)
    import fcntl
    import os
    held = os.open(lock, os.O_CREAT | os.O_WRONLY)
    fcntl.flock(held, fcntl.LOCK_EX)
    outcome = repair_file(src, tmp_path / "o1", make_engine(f"file:{attempts}"),
                          apply=True)
    assert outcome.verified and "apply skipped" in outcome.reason
    assert not sidecar.exists()
    os.close(held)

    # First-backup-wins: the earliest .bak (closest to the user's original)
    # survives later applies. The pre-existing sidecars are whitelist-legal
    # but name the wrong lemma, so each run genuinely repairs and applies.
    original = "lemma Wrong(x: int)\n  ensures x == x\n{\n}\n"
    sidecar.write_text(original)
    outcome = repair_file(src, tmp_path / "o2", make_engine(f"file:{attempts}"),
                          apply=True)
    assert outcome.verified and sidecar.read_text() == GOOD
    bak = tmp_path / "m.proofs.dfy.bak"
    assert bak.read_text() == original
    sidecar.write_text("lemma Wrong2(x: int)\n  ensures x == x\n{\n}\n")
    repair_file(src, tmp_path / "o3", make_engine(f"file:{attempts}"), apply=True)
    assert sidecar.read_text() == GOOD
    assert bak.read_text() == original  # not clobbered by the second apply


def test_apply_first_wins_when_sidecar_changed_mid_repair(tmp_path):
    # A concurrent repair applied its own verified proof while this one
    # ran: nothing is overwritten (first-apply-wins), with a clear reason.
    from lemmapy.repair import _apply_sidecar

    src = tmp_path / "m.py"
    src.write_text("frozen")
    sidecar = tmp_path / "m.proofs.dfy"
    concurrent = "lemma Other(x: int)\n  ensures x == x\n{\n}\n"
    sidecar.write_text(concurrent)
    reason = _apply_sidecar(sidecar, GOOD, None, src, "frozen")
    assert "apply skipped" in reason and "concurrent" in reason
    assert sidecar.read_text() == concurrent  # untouched
    # Matching prior applies normally; identical content is a no-op.
    reason = _apply_sidecar(sidecar, GOOD, concurrent, src, "frozen")
    assert reason == "verified (sidecar applied)"
    assert _apply_sidecar(sidecar, GOOD, GOOD, src, "frozen") \
        == "verified (sidecar already up to date)"


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_source_changed_mid_repair_skips_apply(tmp_path):
    # The engine simulates a concurrent editor save: it edits the LIVE
    # source while proposing the proof. The proof holds for the snapshot,
    # so nothing is installed beside the changed source.
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)

    def editing_engine(request):
        src.write_text(NEEDS_LEMMA + "\n# edited mid-repair\n")
        return GOOD

    outcome = repair_file(src, tmp_path / "out", editing_engine, apply=True)
    assert outcome.verified
    assert "source changed" in outcome.reason
    assert not (tmp_path / "m.proofs.dfy").exists()


def test_orphaned_lock_file_is_inert_held_flock_blocks(tmp_path):
    # A leftover .lock file whose holder died does not block (the kernel
    # released the flock with the process); only a live flock holder does.
    import fcntl
    import os

    from lemmapy.repair import _apply_sidecar

    src = tmp_path / "m.py"
    src.write_text("x")
    sidecar = tmp_path / "m.proofs.dfy"
    lock = tmp_path / "m.proofs.dfy.lock"
    lock.write_text("junk from a dead process")
    assert _apply_sidecar(sidecar, GOOD, None, src, "x") \
        == "verified (sidecar applied)"
    assert sidecar.read_text() == GOOD
    sidecar.unlink()
    held = os.open(lock, os.O_CREAT | os.O_WRONLY)
    fcntl.flock(held, fcntl.LOCK_EX)
    reason = _apply_sidecar(sidecar, GOOD, None, src, "x")
    assert "apply skipped" in reason and not sidecar.exists()
    os.close(held)


def test_source_recheck_under_the_lock(tmp_path):
    # The live source is compared under the lock at the last instant: a
    # mismatch means nothing is written.
    from lemmapy.repair import _apply_sidecar

    src = tmp_path / "m.py"
    src.write_text("edited meanwhile")
    sidecar = tmp_path / "m.proofs.dfy"
    reason = _apply_sidecar(sidecar, GOOD, None, src, "what the loop verified")
    assert "source changed" in reason and not sidecar.exists()


def test_unrepairable_source_stops_immediately(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return len(set(xs))\n"
    )
    engine = make_engine(f"file:{tmp_path / 'unused'}")
    outcome = repair_file(src, tmp_path / "out", engine)
    assert not outcome.verified
    assert outcome.iterations == 0
    assert "not repairable" in outcome.reason


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_reused_workdir_does_not_reuse_stale_sidecar(tmp_path):
    # First run succeeds and leaves a work sidecar; the second run (same
    # outdir, no adjacent sidecar) must start stripped, not inherit it.
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(GOOD)
    outdir = tmp_path / "out"
    assert repair_file(src, outdir, make_engine(f"file:{attempts}")).verified
    empty = tmp_path / "empty"
    empty.mkdir()
    rerun = repair_file(src, outdir, make_engine(f"file:{empty}"))
    assert not rerun.verified  # engine exhausted — no stale zero-iteration win
    assert rerun.iterations == 0 or "engine" in rerun.reason


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_iteration_budget_exhaustion(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(BODILESS)
    (attempts / "2.dfy").write_text(BODILESS)
    engine = make_engine(f"file:{attempts}")
    outcome = repair_file(src, tmp_path / "out", engine, max_iterations=2)
    assert not outcome.verified
    assert outcome.reason == "iteration budget exhausted"


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_repair_attempts_record_rejections(tmp_path):
    # Telemetry: one attempt record per verify; a whitelist-tripping
    # proposal is classified AT PROPOSAL TIME with its rule id. Loop
    # behavior (iterations, history) is unchanged by the recording.
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(BODILESS)  # rejected: axiom
    (attempts / "2.dfy").write_text(GOOD)      # accepted, verifies
    engine = make_engine(f"file:{attempts}")
    outcome = repair_file(src, tmp_path / "out", engine, max_iterations=4)
    assert outcome.verified and outcome.iterations == 2
    assert [a["attempt"] for a in outcome.attempts] == [0, 1, 2]
    assert outcome.attempts[0]["status"] == "encode-error"
    assert outcome.attempts[0]["rejection"]["rule"] == "bodiless"
    assert outcome.attempts[1]["rejection"] is None
    assert outcome.attempts[2]["status"] == "ok"
    assert outcome.attempts[2]["engine_ms"] is None  # no engine call after ok
    assert all(a["verify_ms"] >= 0 for a in outcome.attempts)
    # History shape is what it was before telemetry landed.
    assert any("axiom" in str(h["failures"]) for h in outcome.history[1:])


def test_exhausted_loop_still_counts_last_rejection(tmp_path):
    # The final proposal of an exhausted budget never gets a next-iteration
    # verify payload — proposal-time classification must count it anyway.
    # (Encode-error loops never reach Dafny, so this needs no prover.)
    src = tmp_path / "m.py"
    src.write_text(NEEDS_LEMMA)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(BODILESS)
    (attempts / "2.dfy").write_text(BODILESS)
    engine = make_engine(f"file:{attempts}")
    outcome = repair_file(src, tmp_path / "out", engine, max_iterations=2)
    assert not outcome.verified
    rejections = [a["rejection"] for a in outcome.attempts if a["rejection"]]
    assert len(rejections) == 2  # every proposal counted, including the last
    assert all(r["rule"] == "bodiless" for r in rejections)
