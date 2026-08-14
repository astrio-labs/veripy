"""Proof-repair exams: strip proof additions, score restoration."""

from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.benchmark.exam import (
    exam_tasks,
    render_exam_report,
    run_repair_exam,
    screen_sidecar,
    strip_proof_clauses,
)
from lemmapy.cli import main
from lemmapy.repair import make_engine

REPO = Path(__file__).resolve().parent.parent


ROSTER = ["below_zero", "gcd", "is_prime", "modp", "rolling_max",
          "sum_squares"]


def test_exam_roster_is_the_sidecar_bearing_tasks():
    tasks = exam_tasks(REPO / "benchmark" / "tasks")
    assert [t.name for t in tasks] == ROSTER


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
@pytest.mark.parametrize("task_id", ROSTER)
def test_sidecar_is_load_bearing(task_id, tmp_path):
    # The scientific control for every roster task, and a permanent
    # tripwire against preamble growth making a pack vacuous.
    #
    # This test used to drop the sidecar and assert `status != "ok"`, which
    # it never could be: the `#@ proof` clauses stayed in the source, so the
    # ENCODER rejected the file with "unknown lemma 'X'" before the prover
    # ran. That happens for every task, vacuous or not — the assertion could
    # not fail, and the control measured nothing. `screen_sidecar` strips
    # the clauses too and requires a genuine PROVER failure.
    result = screen_sidecar(REPO / "benchmark" / "tasks" / task_id,
                            time_limit=60)
    assert result.adoptable, f"{task_id}: {result.verdict} — {result.detail}"


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


# -- the screen itself: it must be able to FAIL --------------------------------
#
# The bug this replaces was not a wrong verdict but an impossible one: the
# old control could never report anything but "load-bearing". Each verdict
# below is exercised against a task built to produce it.

TRIVIAL = ("#@ ensures result == x\n"
           "def f(x: int) -> int:\n"
           "    #@ proof Obvious(x)\n"
           "    return x\n")
OBVIOUS = "lemma Obvious(x: int)\n  ensures x == x\n{\n}\n"


def _task(root: Path, name: str, source: str, sidecar: str | None) -> Path:
    d = root / name
    d.mkdir(parents=True)
    (d / "task.py").write_text(source)
    if sidecar is not None:
        (d / "task.proofs.dfy").write_text(sidecar)
    return d


def test_strip_proof_clauses_removes_only_proof_clauses():
    src = ("#@ ensures result == x\n"
           "def f(x: int) -> int:\n"
           "    #@ invariant True\n"
           "    #@ proof Obvious(x)\n"
           "        #@ proof Indented(x)\n"
           "    return x  # @ proof not a clause\n")
    out = strip_proof_clauses(src)
    assert "#@ proof" not in out
    assert "#@ invariant True" in out
    assert "return x  # @ proof not a clause" in out


def test_strip_agrees_with_the_parser_on_what_a_proof_clause_is():
    # The parser splits on whitespace after `#@`, so all three spellings are
    # proof clauses. A prefix match on "#@ proof" leaves the other two behind
    # naming lemmas the stripped file no longer has, the encoder rejects it,
    # and the screen reports `inconclusive` for a task it could have judged.
    src = ("#@ ensures result == x\n"
           "def f(x: int) -> int:\n"
           "    #@proof Obvious(x)\n"
           "    #@  proof Obvious(x)\n"
           "    #@\tproof Obvious(x)\n"
           "    y = x  #@ proof Obvious(x)\n"
           '    """\n'
           "    #@ proof NotAClause(x)\n"
           '    """\n'
           "    return y\n")
    out = strip_proof_clauses(src)
    from lemmapy.frontend.extract import parse_source
    assert not [c for s in parse_source(out).functions
                for c in s.clauses if c.kind == "proof"]
    # A clause trailing real code loses the comment, not the statement; text
    # inside a string literal is not a clause and must survive untouched.
    assert "    y = x\n" in out
    assert "    #@ proof NotAClause(x)\n" in out


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_screen_calls_a_vacuous_pack_vacuous(tmp_path):
    # Z3 proves `result == x` unaided, so the pack does nothing. This is the
    # case the old control was structurally incapable of reporting.
    result = screen_sidecar(_task(tmp_path, "trivial", TRIVIAL, OBVIOUS))
    assert result.verdict == "vacuous" and not result.adoptable
    assert "measures nothing" in result.detail


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_screen_reports_a_broken_task_rather_than_judging_its_pack(tmp_path):
    # Fails WITH the pack: nothing can be concluded about load-bearingness,
    # and calling it "vacuous" would send someone to rewrite the wrong file.
    src = ("#@ ensures result == x + 1\n"
           "def f(x: int) -> int:\n"
           "    #@ proof Obvious(x)\n"
           "    return x\n")
    result = screen_sidecar(_task(tmp_path, "wrong", src, OBVIOUS))
    assert result.verdict == "broken" and "does not verify WITH" in result.detail


def test_screen_needs_a_sidecar_to_screen(tmp_path):
    result = screen_sidecar(_task(tmp_path, "bare", TRIVIAL, None))
    assert result.verdict == "broken" and "no task.proofs.dfy" in result.detail


def test_screen_report_renders_the_failing_verdicts(tmp_path):
    from lemmapy.benchmark.exam import ScreenResult, render_screen_report

    text = render_screen_report([
        ScreenResult("a", "load-bearing", "ok"),
        ScreenResult("b", "vacuous", "proves itself"),
    ])
    assert "load-bearing: 1/2" in text and "vacuous" in text
    assert render_screen_report([]) == "no sidecar-bearing tasks to screen"


@pytest.mark.parametrize("stripped,expected", [
    # The old bug, isolated. A conformance rejection says NOTHING about
    # provability -- and it is exactly what dropping the sidecar alone
    # produced for every task, which is why the old control could not fail.
    ({"status": "encode-error",
      "failures": [{"kind": "conformance", "message": "unknown lemma 'L'"}]},
     "inconclusive"),
    # `failed`, but nothing the taxonomy calls a prover obligation: the
    # prover ran and we still cannot say it needed the pack.
    ({"status": "failed", "failures": [{"kind": "unknown", "message": "?"}]},
     "inconclusive"),
    # The harness fell over. Not a verdict about the task.
    ({"status": "tool-error", "failures": [], "error": "dafny not found"},
     "inconclusive"),
    # `resolution` is in PROVER_KINDS but means the sidecar did not
    # typecheck, so the proof was never attempted. Crediting it would be
    # this screen's own bug one level down: adoptable on no evidence.
    ({"status": "failed",
      "failures": [{"kind": "resolution",
                    "message": "unresolved identifier: Obvious"}]},
     "inconclusive"),
    # ...but a real obligation alongside it still carries the verdict.
    ({"status": "failed",
      "failures": [{"kind": "resolution", "message": "unresolved identifier"},
                   {"kind": "postcondition", "message": "might not hold"}]},
     "load-bearing"),
    ({"status": "ok", "failures": []}, "vacuous"),
    ({"status": "failed",
      "failures": [{"kind": "postcondition", "message": "might not hold"}]},
     "load-bearing"),
])
def test_screen_verdict_table(stripped, expected, tmp_path, monkeypatch):
    # Classification, decoupled from Dafny: what the screen concludes from a
    # given stripped-run payload, given the golden run verified.
    calls = {"n": 0}

    def fake_verify(path, outdir, **kw):
        calls["n"] += 1
        return {"status": "ok", "failures": []} if calls["n"] == 1 else stripped

    monkeypatch.setattr("lemmapy.agentio.verify_structured", fake_verify)
    result = screen_sidecar(_task(tmp_path, "t", TRIVIAL, OBVIOUS))
    assert result.verdict == expected, result.detail
    # Whatever the verdict, the recorded evidence never includes a kind that
    # establishes nothing about provability.
    assert "resolution" not in result.prover_kinds


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_cli_screen_exit_codes(tmp_path, capsys):
    corpus = tmp_path / "tasks"
    _task(corpus, "trivial", TRIVIAL, OBVIOUS)
    assert main(["benchmark", "--tasks", str(corpus), "--screen"]) == 1
    assert "vacuous" in capsys.readouterr().out
    empty = tmp_path / "empty"
    empty.mkdir()
    assert main(["benchmark", "--tasks", str(empty), "--screen"]) == 2
