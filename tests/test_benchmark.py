from pathlib import Path

import pytest

from lemmapy.benchmark.mutate import generate_mutations

CLAMP = (
    "#@ verified\n"
    "#@ requires lo <= hi\n"
    "#@ ensures lo <= result <= hi\n"
    "#@ ensures result == x or result == lo or result == hi\n"
    "def clamp(x: int, lo: int, hi: int) -> int:\n"
    "    return min(max(x, lo), hi)\n"
)


def test_mutation_generation_is_deterministic():
    a = generate_mutations(CLAMP)
    b = generate_mutations(CLAMP)
    assert a == b
    assert len(a) >= 1


def test_mutants_preserve_spec_comments():
    for _desc, mutated in generate_mutations(CLAMP):
        assert "#@ ensures lo <= result <= hi" in mutated
        assert mutated != CLAMP


def test_mutants_all_parse():
    import ast

    for _desc, mutated in generate_mutations(CLAMP, max_mutants=16):
        ast.parse(mutated)


def test_mutation_sites_cover_operators_and_constants():
    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        if i < n - 1:\n"
        "            s = s + 1\n"
        "    return s\n"
    )
    descriptions = [d for d, _ in generate_mutations(src, max_mutants=16)]
    joined = " | ".join(descriptions)
    assert "`<` -> `<=`" in joined
    assert "`-` -> `+`" in joined or "`+` -> `-`" in joined
    assert "`0` -> `1`" in joined or "`1` -> `2`" in joined


def test_errored_mutant_analysis_blocks_the_rung(tmp_path, monkeypatch):
    # An incomplete panel (analysis errors) must not read as passing.
    from lemmapy.benchmark import runner as runner_mod

    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(
        "#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    )
    (task_dir / "meta.json").write_text('{"id": "t"}')

    calls = {"n": 0}

    def fake_hunt(source, name, workdir, timeout):
        calls["n"] += 1
        if calls["n"] == 1:
            return "clean", ""  # R1 on the original passes
        return runner_mod.ERROR, "crosshair exited 2"  # every mutant errors

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=4)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == runner_mod.ERROR
    assert score.height == 2  # gate + hunt only


def test_mixed_survivor_and_error_panel_reports_error(tmp_path, monkeypatch):
    # Survivors + errored analyses: the incomplete panel outranks the
    # ordinary failure, and both facts appear in the detail.
    from lemmapy.benchmark import runner as runner_mod

    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(
        "#@ ensures result >= 0 or result < 0\n"
        "def f(x: int) -> int:\n"
        "    if x > 0:\n"
        "        return x + 1\n"
        "    return x - 2\n"
    )
    (task_dir / "meta.json").write_text('{"id": "t"}')

    verdicts = iter(["clean", "counterexample", "clean", "error-sentinel"])

    def fake_hunt(source, name, workdir, timeout):
        v = next(verdicts, "error-sentinel")
        if v == "error-sentinel":
            return runner_mod.ERROR, "crosshair exited 2"
        return v, ""

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=3)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == runner_mod.ERROR
    assert "survivor" in mutants.detail and "analysis error" in mutants.detail


def test_report_shows_err_not_ratio_for_incomplete_panel():
    # An errored panel's kill count is a lower bound, not a mutation
    # score — the scorecard must say `err`, not render 1/3 like a
    # completed panel. A completed FAIL panel keeps its ratio.
    from lemmapy.benchmark.runner import ERROR, FAIL, PASS, Rung, TaskScore, render_report

    def score(task_id, status):
        s = TaskScore(task_id=task_id)
        s.mutants_total, s.mutants_killed = 3, 1
        s.rungs.append(Rung("gate", PASS, ""))
        s.rungs.append(Rung("mutants", status, ""))
        return s

    report = render_report([score("errored", ERROR), score("survived", FAIL)])
    errored_row = next(l for l in report.splitlines() if l.startswith("errored"))
    survived_row = next(l for l in report.splitlines() if l.startswith("survived"))
    assert "err" in errored_row and "1/3" not in errored_row
    assert "1/3" in survived_row


def test_hunt_unwritable_workdir_degrades_to_error(tmp_path):
    # Staging failures (mkdir/write) must yield a per-item ERROR verdict,
    # not a traceback that aborts the benchmark mid-scorecard.
    from lemmapy.benchmark.runner import ERROR, _hunt

    blocker = tmp_path / "blocker"
    blocker.write_text("")  # a file where the workdir must be a directory
    verdict, detail = _hunt(
        "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n",
        "t", blocker / "sub", per_condition_timeout=1,
    )
    assert verdict == ERROR
    assert "could not stage" in detail


def test_run_benchmark_survives_task_staging_failure(tmp_path):
    # A task whose workdir cannot be created still gets a scorecard row.
    from lemmapy.benchmark.runner import ERROR, run_benchmark

    tasks_root = tmp_path / "tasks"
    task_dir = tasks_root / "t"
    task_dir.mkdir(parents=True)
    (task_dir / "task.py").write_text(
        "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n"
    )
    blocker = tmp_path / "work"
    blocker.write_text("")  # run_task's workdir lands under a file
    scores = run_benchmark(tasks_root, blocker)
    assert len(scores) == 1
    assert scores[0].task_id == "t"
    assert scores[0].rungs[0].status == ERROR
    assert "staging failed" in scores[0].rungs[0].detail
    assert scores[0].height == 0


def test_hunt_subprocess_exception_degrades_to_error(tmp_path, monkeypatch):
    # A stuck CrossHair must not abort the whole run before the scorecard.
    import subprocess as sp

    from lemmapy.benchmark import runner as runner_mod

    def raising_run(cmd, **kwargs):
        raise sp.TimeoutExpired(cmd, 1)

    monkeypatch.setattr(runner_mod.subprocess, "run", raising_run)
    monkeypatch.setattr(runner_mod, "_find_crosshair", lambda: "crosshair")
    verdict, detail = runner_mod._hunt(
        "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n",
        "t", tmp_path, per_condition_timeout=1,
    )
    assert verdict == runner_mod.ERROR
    assert "TimeoutExpired" in detail


def _full_stack_available() -> bool:
    from lemmapy.backends.dafny.driver import find_dafny
    from lemmapy.benchmark.runner import _find_crosshair

    try:
        import _dafny  # noqa: F401
        import hypothesis  # noqa: F401
    except ImportError:
        return False
    return find_dafny() is not None and _find_crosshair() is not None


@pytest.mark.skipif(not _full_stack_available(), reason="full toolchain not installed")
def test_cmd_benchmark_exit_status_mirrors_scorecard(tmp_path, monkeypatch):
    # CI gates on the exit code: 0 all-pass, 1 failed rungs, 2 tool errors.
    import lemmapy.cli as cli
    from lemmapy.benchmark.runner import ERROR, FAIL, PASS, Rung, TaskScore

    def score(status):
        s = TaskScore(task_id="t")
        s.rungs.append(Rung("gate", status, ""))
        return s

    for status, expected in ((PASS, 0), (FAIL, 1), (ERROR, 2)):
        monkeypatch.setattr(
            "lemmapy.benchmark.runner.run_benchmark",
            lambda tasks, outdir, _s=status, **kw: [score(_s)],
        )
        got = cli.cmd_benchmark(tmp_path, tmp_path / "w", report=None,
                                mutant_cap=8, quick=False)
        assert got == expected, f"{status}: expected exit {expected}, got {got}"


def test_bump_climbs_the_full_ladder(tmp_path):
    from lemmapy.benchmark.runner import run_task

    task_dir = Path(__file__).resolve().parent.parent / "benchmark" / "tasks" / "bump"
    score = run_task(task_dir, tmp_path, mutant_cap=2, hunt_timeout=5,
                     dafny_time_limit=30, difftest_examples=15)
    assert score.height == 6, [(r.name, r.status, r.detail) for r in score.rungs]
    assert score.mutants_total >= 1
    assert score.mutants_killed == score.mutants_total
