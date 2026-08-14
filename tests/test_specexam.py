"""Spec-writing exam."""

from lemmapy.benchmark.specexam import SpecExamScore


def test_timeout_bias_check_reports_both_verdicts():
    # A refutation gap is a STRENGTH gap only if both arms concluded on the
    # same mutants. Engine specs can be systematically more expensive to
    # hunt (more quantifiers, wider domains) without being weaker, so an
    # unequal inconclusive count must disqualify the comparison rather than
    # quietly widen the gap.
    from lemmapy.benchmark.specexam import (SpecExamScore,
                                            render_spec_exam_report)

    def row(task_id, killed, engine_timeout=0, golden_timeout=0):
        return SpecExamScore(
            task_id=task_id, valid=True, attempts=1, reason="scored",
            mutants_total=4, mutants_killed=killed,
            mutants_timeout=engine_timeout,
            golden_mutants_total=4, golden_mutants_killed=4,
            golden_mutants_timeout=golden_timeout)

    clean = row("a", 3)
    assert clean.comparable
    report = render_spec_exam_report([clean])
    assert "timeout-bias check: PASSED" in report
    assert "TIMEOUT BIAS" not in report
    assert "3/4!" not in report

    biased = row("b", 1, engine_timeout=2)
    assert not biased.comparable
    report = render_spec_exam_report([clean, biased])
    assert "TIMEOUT BIAS" in report and "b" in report
    assert "1/4!" in report                      # the row is marked
    assert "inconclusive hunts: engine 2, golden 0" in report
    assert "PASSED" not in report

    # Symmetric: golden timing out more must disqualify it just as loudly,
    # since that direction flatters the engine.
    flipped = row("c", 4, golden_timeout=2)
    assert not flipped.comparable
    assert "TIMEOUT BIAS" in render_spec_exam_report([flipped])


def test_timeout_count_covers_adjudicated_and_unadjudicated():
    from lemmapy.benchmark.runner import TaskScore

    score = TaskScore(task_id="t")
    assert score.timeout_count == 0
    score.timeouts = ["line 1 col 2: `+` -> `-`"]
    score.adjudicated_timeouts = 2
    # An adjudicated divergence is still an inconclusive HUNT: the wall was
    # exhausted, and a human ruled it afterwards. Both count for bias.
    assert score.timeout_count == 3
