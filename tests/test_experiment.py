"""The experiment harness: arms, JSONL ledger, matrix driver, resume."""

import json
import shutil
from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.benchmark.exam import ExamScore
from lemmapy.benchmark.experiment import (
    ARMS,
    _AblatedEngine,
    completed_cells,
    redact_failures,
    run_experiment,
    summarize_ledger,
)
from lemmapy.cli import main
from lemmapy.repair import build_request, make_engine, repair_file

TASK_SRC = (
    "#@ ensures result == x\n"
    "def f(x: int) -> int:\n"
    "    #@ proof Obvious(x)\n"
    "    return x\n"
)
GOLDEN = "lemma Obvious(x: int)\n  ensures x == x\n{\n}\n"


def _mini_corpus(tmp_path, names=("mini",)):
    corpus = tmp_path / "tasks"
    for name in names:
        d = corpus / name
        d.mkdir(parents=True)
        (d / "task.py").write_text(TASK_SRC)
        (d / "task.proofs.dfy").write_text(GOLDEN)
    return corpus


def test_wilson_interval_is_defensible_at_small_n():
    from lemmapy.benchmark.experiment import wilson_interval

    # The whole reason not to use the normal approximation: 5/5 must not
    # claim certainty from five observations.
    lo, hi = wilson_interval(5, 5)
    assert hi == 1.0
    assert 0.4 < lo < 0.6, f"5/5 lower bound implausible: {lo}"
    # 0/5 is the mirror image, and stays inside [0, 1].
    lo, hi = wilson_interval(0, 5)
    assert lo == 0.0 and 0.4 < hi < 0.6
    # Symmetric around a half, and tightening with n.
    lo_small, hi_small = wilson_interval(5, 10)
    lo_big, hi_big = wilson_interval(50, 100)
    assert abs((lo_small + hi_small) / 2 - 0.5) < 1e-9
    assert (hi_big - lo_big) < (hi_small - lo_small)
    # No trials is total ignorance, not a crash or a false 0%.
    assert wilson_interval(0, 0) == (0.0, 1.0)


def test_redaction_strips_failure_detail_preserves_contract():
    # Build through build_request so this test trips if the request schema
    # drifts. Structured detail must vanish; loop state must survive.
    payload = {
        "schema": "lemmapy-failures/1", "status": "failed",
        "failures": [{"kind": "postcondition", "function": "f",
                      "py_line": 3, "message": "secret detail"}],
        "sidecar": {"text": "lemma Old()\n{\n}\n"},
    }
    history = [{"attempt": 0, "failures": payload["failures"],
                "proposal": "lemma P()\n{\n}\n"}]
    request = build_request("SOURCE", payload, 1, history)
    redacted = redact_failures(request)
    flat = json.dumps(redacted)
    assert "secret detail" not in flat
    assert "postcondition" not in flat
    # Kept: rules, source, current sidecar, attempt counter, own proposals.
    assert redacted["rules"] == request["rules"]
    assert redacted["source"] == "SOURCE"
    assert redacted["sidecar"] == "lemma Old()\n{\n}\n"
    assert redacted["attempt"] == 1
    assert redacted["history"][0]["proposal"] == "lemma P()\n{\n}\n"
    assert redacted["history"][0]["failures"] == "verification failed"
    assert redacted["failures"]["status"] == "failed"
    assert redacted["failures"]["message"] == "verification failed"
    # The original request is untouched (no aliasing surprises).
    assert request["failures"]["failures"][0]["message"] == "secret detail"


def test_ablated_engine_sees_generic_failures_only(tmp_path, monkeypatch):
    import lemmapy.repair as repair_mod

    payloads = iter([
        {"status": "failed",
         "failures": [{"kind": "invariant", "message": "loop detail"}],
         "sidecar": {"text": ""}},
        {"status": "ok", "failures": [], "sidecar": {"text": ""}},
    ])
    monkeypatch.setattr(repair_mod, "verify_structured",
                        lambda *a, **k: next(payloads))
    seen = []

    def spy(request):
        seen.append(request)
        return GOLDEN

    src = tmp_path / "m.py"
    src.write_text(TASK_SRC)
    outcome = repair_file(src, tmp_path / "out", _AblatedEngine(spy))
    assert outcome.verified
    assert len(seen) == 1
    assert seen[0]["failures"]["message"] == "verification failed"
    assert "loop detail" not in json.dumps(seen[0])


def test_ablated_engine_passes_usage_through():
    class Inner:
        usage_log = [{"output_tokens": 5}]

        def __call__(self, request):
            return GOLDEN

    wrapped = _AblatedEngine(Inner())
    assert wrapped.usage_log == [{"output_tokens": 5}]


def _fake_exam(record):
    """A run_repair_exam stand-in recording its call config."""

    def fake(tasks_root, workdir, factory, max_iterations=4, time_limit=60,
             only=None):
        record.append({"workdir": workdir, "max_iterations": max_iterations,
                       "only": set(only) if only else None})
        engine = factory()  # arms must construct their engine shape
        record[-1]["engine_type"] = type(engine).__name__
        return [ExamScore(task_id=t, restored=True, iterations=1,
                          reason="verified", golden_lemmas=["Obvious"],
                          attempts=[{"attempt": 0, "status": "encode-error",
                                     "failure_kinds": ["conformance"],
                                     "verify_ms": 1, "engine_ms": 2,
                                     "rejection": None}],
                          wall_ms=3, usage=[None])
                for t in sorted(only or [])]

    return fake


def test_matrix_covers_cells_and_arm_configs(tmp_path, monkeypatch):
    import lemmapy.benchmark.experiment as exp_mod

    record = []
    monkeypatch.setattr(exp_mod, "run_repair_exam", _fake_exam(record))
    corpus = _mini_corpus(tmp_path, names=("alpha", "beta"))
    ledger = tmp_path / "ledger.jsonl"
    empty = tmp_path / "empty"
    empty.mkdir()
    written = run_experiment(
        corpus, tmp_path / "cells", [f"file:{empty}"],
        ["full", "one-shot", "ablated"], 2, ledger, max_iterations=4)
    # 3 arms x 2 trials cells, each covering 2 tasks.
    assert len(record) == 6
    assert len(written) == 12
    # one-shot forces a single iteration; the other arms keep the budget.
    by_iters = sorted(c["max_iterations"] for c in record)
    assert by_iters == [1, 1, 4, 4, 4, 4]
    # ablated cells construct the wrapper engine.
    assert sum(1 for c in record if c["engine_type"] == "_AblatedEngine") == 2
    # Cell workdirs are disjoint per (engine, arm, trial).
    assert len({str(c["workdir"]) for c in record}) == 6
    # The ledger holds a run header plus one row per (task, cell).
    lines = [json.loads(l) for l in ledger.read_text().splitlines()]
    headers = [l for l in lines if l["schema"] == "lemmapy-exam-run/1"]
    rows = [l for l in lines if l["schema"] == "lemmapy-exam-trial/1"]
    assert len(headers) == 1 and len(rows) == 12
    assert headers[0]["roster"] == ["alpha", "beta"]
    assert {r["task"] for r in rows} == {"alpha", "beta"}
    assert {r["arm"] for r in rows} == set(ARMS)
    assert all(r["proposals"] == 1 for r in rows)


def test_ledger_append_resume_and_torn_tail(tmp_path, monkeypatch):
    import lemmapy.benchmark.experiment as exp_mod

    record = []
    monkeypatch.setattr(exp_mod, "run_repair_exam", _fake_exam(record))
    corpus = _mini_corpus(tmp_path)
    ledger = tmp_path / "ledger.jsonl"
    empty = tmp_path / "empty"
    empty.mkdir()
    args = (corpus, tmp_path / "cells", [f"file:{empty}"], ["full"], 2, ledger)
    first = run_experiment(*args)
    assert len(first) == 2
    # A torn tail line (crash mid-append) must not poison resume.
    with open(ledger, "a") as fh:
        fh.write('{"schema": "lemmapy-exam-trial/1", "exam": "proof-re')
    second = run_experiment(*args)
    assert second == []  # everything already recorded -> nothing re-run
    assert len(record) == 2  # no third/fourth exam invocation
    third = run_experiment(*args, resume=False)
    assert len(third) == 2  # explicit re-run appends fresh rows
    done = completed_cells(ledger)
    assert ("proof-repair", "mini", f"file:{empty}", "full", 0) in done


def test_unknown_task_filter_and_missing_roster_rejected(tmp_path):
    corpus = _mini_corpus(tmp_path)
    ledger = tmp_path / "ledger.jsonl"
    with pytest.raises(ValueError, match="unknown task"):
        run_experiment(corpus, tmp_path / "cells", ["file:/tmp/x"], ["full"],
                       1, ledger, only_tasks={"nonesuch"})
    bare = tmp_path / "bare"
    bare.mkdir()
    with pytest.raises(ValueError, match="no proof-repair exam tasks"):
        run_experiment(bare, tmp_path / "cells", ["file:/tmp/x"], ["full"],
                       1, ledger)
    with pytest.raises(ValueError, match="unknown arm"):
        run_experiment(corpus, tmp_path / "cells", ["file:/tmp/x"], ["bogus"],
                       1, ledger)
    with pytest.raises(ValueError, match="unknown engine"):
        run_experiment(corpus, tmp_path / "cells", ["gpt"], ["full"], 1, ledger)
    with pytest.raises(ValueError, match="unknown exam"):
        run_experiment(corpus, tmp_path / "cells", ["file:/tmp/x"], ["full"],
                       1, ledger, exam="vibes")
    # The loop arms are meaningless for a one-shot exam and are refused
    # rather than silently collapsed.
    with pytest.raises(ValueError, match="unknown arm .* for exam"):
        run_experiment(corpus, tmp_path / "cells", ["file:/tmp/x"],
                       ["ablated"], 1, ledger, exam="spec-writing")
    assert not ledger.exists()  # config errors precede any ledger write


def test_experiment_refuses_corpus_overlap(tmp_path):
    corpus = _mini_corpus(tmp_path)
    ledger = tmp_path / "ledger.jsonl"
    with pytest.raises(ValueError, match="overlaps the task corpus"):
        run_experiment(corpus, corpus / "cells", ["file:/tmp/x"], ["full"],
                       1, ledger)
    assert (corpus / "mini" / "task.py").exists()


def test_summarize_groups_and_rejection_breakdown(tmp_path, monkeypatch):
    import lemmapy.benchmark.experiment as exp_mod

    def fake(tasks_root, workdir, factory, max_iterations=4, time_limit=60,
             only=None):
        factory()
        return [ExamScore(
            task_id=t, restored=False, iterations=2, reason="exhausted",
            golden_lemmas=["Obvious"],
            attempts=[
                {"attempt": 0, "status": "encode-error", "failure_kinds": [],
                 "verify_ms": 1, "engine_ms": 2,
                 "rejection": {"rule": "bodiless", "message": "axiom"}},
                {"attempt": 1, "status": "encode-error", "failure_kinds": [],
                 "verify_ms": 1, "engine_ms": 2,
                 "rejection": {"rule": "forbidden-token", "message": "assume"}},
            ],
            wall_ms=3,
            usage=[{"input_tokens": 10, "output_tokens": 5, "cost_usd": 0.01},
                   {"input_tokens": 20, "output_tokens": 7, "cost_usd": 0.02}],
        ) for t in sorted(only or [])]

    monkeypatch.setattr(exp_mod, "run_repair_exam", fake)
    corpus = _mini_corpus(tmp_path)
    ledger = tmp_path / "ledger.jsonl"
    empty = tmp_path / "empty"
    empty.mkdir()
    run_experiment(corpus, tmp_path / "cells", [f"file:{empty}"], ["full"],
                   1, ledger)
    table = summarize_ledger(ledger)
    assert "0/1" in table
    assert "ok (restored/valid): 0/1" in table
    assert "bodiless: 1" in table and "forbidden-token: 1" in table
    assert "100" in table  # 2 rejections / 2 proposals
    rows = [json.loads(l) for l in ledger.read_text().splitlines()
            if json.loads(l).get("schema") == "lemmapy-exam-trial/1"]
    assert rows[0]["usage_total"] == {"input_tokens": 30, "output_tokens": 12,
                                      "cost_usd": 0.03}


def test_resume_does_not_hide_failed_cells(tmp_path, capsys):
    """A resumed run must not report success over an earlier run's failures.

    `run_experiment` returns only NEWLY written rows so resume stays
    idempotent; judging exit status by that list means a second invocation
    — which re-runs nothing — reports a clean pass while the ledger still
    holds failed trials. CI would accept an unsuccessful matrix.
    """
    corpus = _mini_corpus(tmp_path)
    empty = tmp_path / "empty"
    empty.mkdir()
    argv = ["experiment", "--tasks", str(corpus), "-o", str(tmp_path / "o"),
            "--engines", f"file:{empty}", "--arms", "full", "--trials", "1"]

    # First run: the file engine is exhausted, so the cell fails.
    assert main(argv) == 1
    capsys.readouterr()

    # Second run: every cell is already in the ledger, so nothing re-runs
    # and no rows are written — but the matrix still contains a failure.
    assert main(argv) == 1
    out = capsys.readouterr()
    assert "0 cell-task row(s) appended" in out.out
    assert "1 resumed from earlier runs" in out.out
    assert "did not succeed" in out.err


def test_resume_reports_success_when_the_matrix_passed(tmp_path, monkeypatch):
    # The mirror case: a fully-resumed matrix of successes must exit 0, not
    # fall through the "nothing recorded" branch.
    import lemmapy.benchmark.experiment as exp_mod

    monkeypatch.setattr(exp_mod, "run_repair_exam", _fake_exam([]))
    corpus = _mini_corpus(tmp_path)
    empty = tmp_path / "empty"
    empty.mkdir()
    argv = ["experiment", "--tasks", str(corpus), "-o", str(tmp_path / "o"),
            "--engines", f"file:{empty}", "--arms", "full", "--trials", "1"]
    assert main(argv) == 0
    assert main(argv) == 0  # resumed, still passing


def test_stale_task_rows_do_not_fail_the_current_matrix(tmp_path, capsys):
    """A ledger outlives the corpus; a dropped task must not fail today's run.

    Ledgers are append-only, so a task later renamed or removed keeps its
    historical rows forever. Scoping the status query by "every task in the
    ledger" would let one of those rows fail a matrix that no longer
    contains the task at all.
    """
    corpus = _mini_corpus(tmp_path, names=("alpha", "retired"))
    empty = tmp_path / "empty"
    empty.mkdir()
    argv = ["experiment", "--tasks", str(corpus), "-o", str(tmp_path / "o"),
            "--engines", f"file:{empty}", "--arms", "full", "--trials", "1"]

    # Both tasks fail (engine exhausted), so both are recorded unsuccessful.
    assert main(argv) == 1
    capsys.readouterr()

    # `retired` leaves the corpus; its failing row stays in the ledger.
    shutil.rmtree(corpus / "retired")

    # Replace alpha's cell with a success, simulating a fixed re-run.
    ledger = tmp_path / "o" / "ledger.jsonl"
    rows = [json.loads(l) for l in ledger.read_text().splitlines()]
    for row in rows:
        if row.get("task") == "alpha":
            row["restored"] = True
    ledger.write_text("\n".join(json.dumps(r) for r in rows) + "\n")

    # The current matrix is {alpha}, which passes. `retired`'s stale
    # failure must not be counted.
    assert main(argv) == 0
    out = capsys.readouterr().out
    assert "ok (restored/valid)" in out


def test_matrix_rows_scopes_to_the_requested_cells(tmp_path, monkeypatch):
    import lemmapy.benchmark.experiment as exp_mod
    from lemmapy.benchmark.experiment import matrix_rows

    monkeypatch.setattr(exp_mod, "run_repair_exam", _fake_exam([]))
    corpus = _mini_corpus(tmp_path, names=("alpha", "beta"))
    ledger = tmp_path / "ledger.jsonl"
    empty = tmp_path / "empty"
    empty.mkdir()
    spec = f"file:{empty}"
    run_experiment(corpus, tmp_path / "cells", [spec], ["full", "one-shot"],
                   2, ledger)
    everything = matrix_rows(ledger, exam="proof-repair", engines=[spec],
                             arms=["full", "one-shot"], trials=2)
    assert len(everything) == 8  # 2 tasks x 2 arms x 2 trials
    # Narrowing any axis narrows the matrix; other exams never leak in.
    assert len(matrix_rows(ledger, exam="proof-repair", engines=[spec],
                           arms=["full"], trials=2)) == 4
    assert len(matrix_rows(ledger, exam="proof-repair", engines=[spec],
                           arms=["full", "one-shot"], trials=1)) == 4
    assert len(matrix_rows(ledger, exam="proof-repair", engines=[spec],
                           arms=["full", "one-shot"], trials=2,
                           tasks={"alpha"})) == 4
    assert matrix_rows(ledger, exam="spec-writing", engines=[spec],
                       arms=["one-shot"], trials=2) == []
    assert matrix_rows(ledger, exam="proof-repair", engines=["claude"],
                       arms=["full"], trials=2) == []
    assert matrix_rows(tmp_path / "nonesuch.jsonl", exam="proof-repair",
                       engines=[spec], arms=["full"], trials=2) == []


def test_cli_experiment_exit_codes_and_summary(tmp_path, capsys):
    # An exhausted file engine on an encode-error loop needs no prover:
    # the full CLI path runs (matrix -> ledger -> summary) and exits 1.
    corpus = _mini_corpus(tmp_path)
    empty = tmp_path / "empty"
    empty.mkdir()
    status = main(["experiment", "--tasks", str(corpus),
                   "-o", str(tmp_path / "o"),
                   "--engines", f"file:{empty}", "--arms", "full",
                   "--trials", "1"])
    out = capsys.readouterr().out
    assert status == 1
    assert "ok (restored/valid): 0/1" in out
    assert (tmp_path / "o" / "ledger.jsonl").exists()
    # Summarize-only mode re-reads the ledger without running cells.
    status = main(["experiment", "--summarize",
                   str(tmp_path / "o" / "ledger.jsonl")])
    assert status == 0
    assert "ok (restored/valid): 0/1" in capsys.readouterr().out
    # A missing ledger is a config error.
    assert main(["experiment", "--summarize",
                 str(tmp_path / "nonesuch.jsonl")]) == 2


def test_spec_writing_matrix_records_strength(tmp_path, monkeypatch):
    import lemmapy.benchmark.experiment as exp_mod
    from lemmapy.benchmark.specexam import SpecExamScore

    seen = []

    def fake_spec_exam(tasks_root, workdir, factory, retries=2, only=None,
                       **ladder):
        seen.append({"retries": retries, "ladder": ladder,
                     "only": set(only or [])})
        factory()
        return [SpecExamScore(
            task_id=t, valid=True, attempts=1, reason="scored", height=3,
            mutants_total=4, mutants_killed=1, survivors=["line 4: `<` -> `<=`"],
            golden_height=6, golden_mutants_total=4, golden_mutants_killed=4,
            clause_counts={"ensures": 1}, wall_ms=5,
            usage=[{"input_tokens": 9, "output_tokens": 3, "cost_usd": 0.02}],
        ) for t in sorted(only or [])]

    monkeypatch.setattr(exp_mod, "run_spec_exam", fake_spec_exam)
    corpus = _mini_corpus(tmp_path, names=("alpha", "beta"))
    ledger = tmp_path / "ledger.jsonl"
    empty = tmp_path / "empty"
    empty.mkdir()
    written = run_experiment(corpus, tmp_path / "cells", [f"file:{empty}"],
                             ["one-shot"], 1, ledger, exam="spec-writing",
                             retries=1, ladder={"mutant_cap": 4})
    assert len(written) == 2
    assert seen[0]["retries"] == 1 and seen[0]["ladder"] == {"mutant_cap": 4}
    assert all(r["exam"] == "spec-writing" for r in written)
    assert all(r["restored"] for r in written)  # `restored` == exam validity
    assert written[0]["mutants_killed"] == 1
    table = summarize_ledger(ledger)
    # Engine strength and golden strength are reported side by side.
    assert "25%" in table and "100%" in table
    assert "spec strength: engine 25% vs golden 100%" in table
    # Resume keys are exam-scoped: the same task/engine/arm/trial in the
    # OTHER exam must not be treated as already done.
    assert ("spec-writing", "alpha", f"file:{empty}", "one-shot", 0) \
        in completed_cells(ledger)
    assert ("proof-repair", "alpha", f"file:{empty}", "one-shot", 0) \
        not in completed_cells(ledger)


def test_failed_spec_answer_scores_zero_against_goldens_panel(tmp_path,
                                                              monkeypatch):
    """A malformed or refuted answer must score 0/N, never vanish.

    Dropping it from the engine's denominator while golden keeps its full
    panel makes FAILING the profitable move: an engine that answers only
    the tasks it is sure of would outscore one that attempts them all.
    """
    import lemmapy.benchmark.experiment as exp_mod
    from lemmapy.benchmark.specexam import SpecExamScore

    def fake_spec_exam(tasks_root, workdir, factory, retries=2, only=None,
                       **ladder):
        factory()
        return [SpecExamScore(
            task_id=t, valid=(t == "alpha"), attempts=1,
            reason="scored" if t == "alpha" else "freeze: changed",
            height=3 if t == "alpha" else 0,
            mutants_total=4 if t == "alpha" else 0,
            mutants_killed=4 if t == "alpha" else 0,
            golden_height=6, golden_mutants_total=4, golden_mutants_killed=4,
        ) for t in sorted(only or [])]

    monkeypatch.setattr(exp_mod, "run_spec_exam", fake_spec_exam)
    corpus = _mini_corpus(tmp_path, names=("alpha", "beta"))
    ledger = tmp_path / "ledger.jsonl"
    empty = tmp_path / "empty"
    empty.mkdir()
    written = run_experiment(corpus, tmp_path / "cells", [f"file:{empty}"],
                             ["one-shot"], 1, ledger, exam="spec-writing")
    # The failed task carries golden's panel as its denominator.
    beta = next(r for r in written if r["task"] == "beta")
    assert beta["mutants_total"] == 4 and beta["mutants_killed"] == 0
    table = summarize_ledger(ledger)
    assert "spec strength: engine 50%" in table   # 4 refuted of 8 attempted
    assert "ok (restored/valid): 1/2" in table    # validity reported separately


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_exam_score_carries_attempts_and_wall(tmp_path):
    corpus = _mini_corpus(tmp_path)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(GOLDEN)
    from lemmapy.benchmark.exam import run_repair_exam

    scores = run_repair_exam(corpus, tmp_path / "work",
                             lambda: make_engine(f"file:{attempts}"),
                             time_limit=30)
    (s,) = scores
    assert s.restored
    assert [a["attempt"] for a in s.attempts] == [0, 1]
    assert s.attempts[0]["engine_ms"] is not None
    assert s.wall_ms > 0
    assert s.usage == []  # file engine reports no usage


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_full_matrix_with_prover_restores_and_resumes(tmp_path):
    corpus = _mini_corpus(tmp_path)
    attempts = tmp_path / "attempts"
    attempts.mkdir()
    (attempts / "1.dfy").write_text(GOLDEN)
    ledger = tmp_path / "ledger.jsonl"
    spec = f"file:{attempts}"
    written = run_experiment(corpus, tmp_path / "cells", [spec],
                             ["full", "one-shot"], 1, ledger, time_limit=30)
    assert len(written) == 2
    assert all(r["restored"] for r in written)
    # one-shot restored too: the single proposal was the golden pack.
    assert {r["arm"] for r in written} == {"full", "one-shot"}
    assert run_experiment(corpus, tmp_path / "cells", [spec],
                          ["full", "one-shot"], 1, ledger,
                          time_limit=30) == []
