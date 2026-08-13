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


def test_make_engine_specs():
    assert callable(make_engine("claude"))
    assert callable(make_engine("file:/tmp/x"))
    with pytest.raises(ValueError, match="unknown engine"):
        make_engine("gpt")


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
