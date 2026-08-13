"""Proof-repair exams: strip proof additions, score restoration."""

from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.benchmark.exam import exam_tasks, render_exam_report, run_repair_exam
from lemmapy.cli import main
from lemmapy.repair import make_engine

REPO = Path(__file__).resolve().parent.parent


def test_exam_roster_is_the_sidecar_bearing_tasks():
    tasks = exam_tasks(REPO / "benchmark" / "tasks")
    assert [t.name for t in tasks] == ["gcd"]


def test_empty_roster_renders_honestly(tmp_path):
    assert "no sidecar-bearing tasks" in render_exam_report([])


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_exam_strips_sidecar_and_scores_restoration(tmp_path):
    # A mini corpus: one task whose #@ proof clause needs a sidecar lemma.
    corpus = tmp_path / "tasks"
    task = corpus / "mini"
    task.mkdir(parents=True)
    (task / "task.py").write_text(
        "#@ ensures result == x\n"
        "def f(x: int) -> int:\n"
        "    #@ proof Obvious(x)\n"
        "    y = x\n"
        "    return y\n"
    )
    golden = "lemma Obvious(x: int)\n  ensures x == x\n{\n}\n"
    (task / "task.proofs.dfy").write_text(golden)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(golden)
    scores = run_repair_exam(corpus, tmp_path / "work",
                             make_engine(f"file:{attempts}"), time_limit=30)
    assert len(scores) == 1
    s = scores[0]
    assert s.restored and s.iterations == 1
    assert s.golden_lemmas == ["Obvious"]
    # The golden sidecar itself was never visible to the engine's task copy.
    assert not (tmp_path / "work" / "mini" / "task.proofs.dfy").exists()


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_gcd_exam_restores_with_scripted_golden_pack(tmp_path):
    # The real corpus exam: strip gcd's 8-lemma divisibility pack, restore
    # it via a scripted engine playing the golden sidecar, and re-earn the
    # proof through the whitelist + prover.
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    golden = (REPO / "benchmark" / "tasks" / "gcd" / "task.proofs.dfy").read_text()
    (attempts / "1.dfy").write_text(golden)
    scores = run_repair_exam(REPO / "benchmark" / "tasks", tmp_path / "work",
                             make_engine(f"file:{attempts}"), time_limit=60)
    assert [s.task_id for s in scores] == ["gcd"]
    assert scores[0].restored and scores[0].iterations == 1
    assert len(scores[0].golden_lemmas) == 8


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_cli_exam_exit_codes(tmp_path, capsys):
    corpus = tmp_path / "tasks"
    task = corpus / "mini"
    task.mkdir(parents=True)
    (task / "task.py").write_text(
        "#@ ensures result == x\n"
        "def f(x: int) -> int:\n"
        "    #@ proof Obvious(x)\n"
        "    return x\n"
    )
    (task / "task.proofs.dfy").write_text(
        "lemma Obvious(x: int)\n  ensures x == x\n{\n}\n")
    empty = tmp_path / "empty"
    empty.mkdir()
    status = main(["benchmark", "--tasks", str(corpus), "-o", str(tmp_path / "o"),
                   "--exam", "proof-repair", "--engine", f"file:{empty}"])
    assert status == 1  # engine exhausted -> not restored
    assert "restored: 0/1" in capsys.readouterr().out
