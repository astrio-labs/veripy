"""Proof-repair exams: strip proof additions, score restoration."""

from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.benchmark.exam import exam_tasks, render_exam_report, run_repair_exam
from lemmapy.cli import main
from lemmapy.repair import make_engine

REPO = Path(__file__).resolve().parent.parent


ROSTER = ["below_zero", "gcd", "is_prime", "modp", "rolling_max",
          "sum_squares", "sum_to_n"]


def test_exam_roster_is_the_sidecar_bearing_tasks():
    tasks = exam_tasks(REPO / "benchmark" / "tasks")
    assert [t.name for t in tasks] == ROSTER


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
@pytest.mark.parametrize("task_id", ROSTER)
def test_sidecar_is_load_bearing(task_id, tmp_path):
    # The scientific control for every roster task — and a permanent
    # tripwire against preamble growth making a sidecar vacuous: WITHOUT
    # its sidecar the task must NOT verify (else the exam row measures
    # nothing).
    from lemmapy.agentio import verify_structured

    src = tmp_path / "task.py"
    src.write_text(
        (REPO / "benchmark" / "tasks" / task_id / "task.py").read_text())
    payload = verify_structured(src, tmp_path / "out", time_limit=60)
    assert payload["status"] != "ok", (
        f"{task_id} verifies WITHOUT its sidecar — the golden pack is "
        f"vacuous and the exam row would measure nothing")


def test_workdir_overlapping_corpus_refused(tmp_path):
    # --tasks pointed at (or inside) the workdir would let the per-task
    # cleanup delete golden sources; refused before anything is touched.
    corpus = tmp_path / "tasks"
    d = corpus / "mini"
    d.mkdir(parents=True)
    (d / "task.py").write_text("#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (d / "task.proofs.dfy").write_text("lemma L(x: int)\n  ensures x == x\n{\n}\n")
    for bad_work in (corpus, corpus / "mini", tmp_path):
        with pytest.raises(ValueError, match="overlaps the task corpus"):
            run_repair_exam(corpus, bad_work, lambda: make_engine("file:/tmp/x"))
    assert (d / "task.py").exists() and (d / "task.proofs.dfy").exists()


def test_symlinked_workspace_cannot_reach_corpus(tmp_path):
    # A symlink planted at <workdir>/<task_id> pointing at the golden task
    # is removed as a LINK; the target survives and the exam proceeds.
    corpus = tmp_path / "tasks"
    d = corpus / "mini"
    d.mkdir(parents=True)
    (d / "task.py").write_text(
        "#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (d / "task.proofs.dfy").write_text(
        "lemma L(x: int)\n  ensures x == x\n{\n}\n")
    work = tmp_path / "work"
    work.mkdir()
    (work / "mini").symlink_to(d)
    empty = tmp_path / "empty"
    empty.mkdir()
    run_repair_exam(corpus, work, lambda: make_engine(f"file:{empty}"),
                    time_limit=5)
    assert (d / "task.py").exists() and (d / "task.proofs.dfy").exists()
    assert not (work / "mini").is_symlink()  # replaced by a real workspace


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
                             lambda: make_engine(f"file:{attempts}"), time_limit=30)
    assert len(scores) == 1
    s = scores[0]
    assert s.restored and s.iterations == 1
    assert s.golden_lemmas == ["Obvious"]
    # The golden sidecar itself was never visible to the engine's task copy.
    assert not (tmp_path / "work" / "mini" / "task.proofs.dfy").exists()


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_gcd_exam_restores_with_scripted_golden_pack(tmp_path):
    # The real corpus exam: strip every roster task's lemma pack, restore
    # it via a scripted engine playing the golden sidecar, and re-earn the
    # proof through the whitelist + prover.
    #
    # One scripted-attempt dir per task; a factory closes over the roster
    # order so each task replays its own golden pack. Assertions are
    # roster-DRIVEN rather than hardcoded, so growing the corpus does not
    # need this test edited — only ROSTER, which is pinned separately.
    tasks_root = REPO / "benchmark" / "tasks"
    roster = [t.name for t in exam_tasks(tasks_root)]
    dirs = []
    for name in roster:
        d = tmp_path / f"attempts_{name}"
        d.mkdir()
        (d / "1.dfy").write_text((tasks_root / name / "task.proofs.dfy").read_text())
        dirs.append(d)
    it = iter(dirs)
    scores = run_repair_exam(tasks_root, tmp_path / "work",
                             lambda: make_engine(f"file:{next(it)}"), time_limit=60)
    assert [s.task_id for s in scores] == roster
    assert all(s.restored and s.iterations == 1 for s in scores)
    # Every roster pack declares at least one lemma, else the `#@ proof`
    # clause it is supposed to satisfy names nothing.
    assert all(s.golden_lemmas for s in scores)


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_multi_task_roster_gets_fresh_engine_per_task(tmp_path):
    # Two identical tasks, one scripted attempt file: with a per-task
    # engine factory BOTH restore (each replays 1.dfy); a shared stateful
    # engine would exhaust on the second.
    corpus = tmp_path / "tasks"
    task_src = (
        "#@ ensures result == x\n"
        "def f(x: int) -> int:\n"
        "    #@ proof Obvious(x)\n"
        "    return x\n"
    )
    golden = "lemma Obvious(x: int)\n  ensures x == x\n{\n}\n"
    for name in ("alpha", "beta"):
        d = corpus / name
        d.mkdir(parents=True)
        (d / "task.py").write_text(task_src)
        (d / "task.proofs.dfy").write_text(golden)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(golden)
    scores = run_repair_exam(corpus, tmp_path / "work",
                             lambda: make_engine(f"file:{attempts}"),
                             time_limit=30)
    assert [s.restored for s in scores] == [True, True]


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_exam_rerun_starts_stripped(tmp_path):
    corpus = tmp_path / "tasks"
    d = corpus / "mini"
    d.mkdir(parents=True)
    (d / "task.py").write_text(
        "#@ ensures result == x\n"
        "def f(x: int) -> int:\n"
        "    #@ proof Obvious(x)\n"
        "    return x\n"
    )
    golden = "lemma Obvious(x: int)\n  ensures x == x\n{\n}\n"
    (d / "task.proofs.dfy").write_text(golden)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(golden)
    work = tmp_path / "work"
    first = run_repair_exam(corpus, work, lambda: make_engine(f"file:{attempts}"),
                            time_limit=30)
    assert first[0].restored
    # Rerun with an exhausted engine: a stale workspace proof must not score.
    empty = tmp_path / "empty"
    empty.mkdir()
    second = run_repair_exam(corpus, work, lambda: make_engine(f"file:{empty}"),
                             time_limit=30)
    assert not second[0].restored


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
