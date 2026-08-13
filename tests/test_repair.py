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
