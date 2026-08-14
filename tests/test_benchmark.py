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

    def fake_hunt(source, name, workdir, timeout, wall=None):
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


def test_analysis_error_reason_is_reported(tmp_path, monkeypatch):
    # "1 analysis error(s)" with no reason is unactionable: a real
    # intermittent failure on main could not be diagnosed because the
    # mutant hunt's reason was discarded. The rung must name it.
    from lemmapy.benchmark import runner as runner_mod

    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(
        "#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    )
    (task_dir / "meta.json").write_text('{"id": "t"}')
    calls = {"n": 0}

    def fake_hunt(source, name, workdir, timeout, wall=None):
        calls["n"] += 1
        if calls["n"] == 1:
            return "clean", ""  # R1 on the original
        if calls["n"] == 2:
            return runner_mod.ERROR, "crosshair exited 137"
        return "counterexample", ""

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=4)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == runner_mod.ERROR
    assert "crosshair exited 137" in mutants.detail
    # ...and the offending mutant is named alongside its reason.
    assert "line " in mutants.detail.split("errors:")[1]


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

    def fake_hunt(source, name, workdir, timeout, wall=None):
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


def test_unadjudicated_timeout_fails_the_rung(tmp_path, monkeypatch):
    # A wall exhaustion is inconclusive (R4 proves the ORIGINAL terminates,
    # not the mutant): without human adjudication it fails the rung, like a
    # survivor, with guidance pointing at meta.json.
    from lemmapy.benchmark import runner as runner_mod

    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(
        "#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    )
    (task_dir / "meta.json").write_text('{"id": "t"}')
    calls = {"n": 0}

    def fake_hunt(source, name, workdir, timeout, wall=None):
        calls["n"] += 1
        if calls["n"] == 1:
            return "clean", ""  # R1 on the original
        if calls["n"] == 2:
            return "timeout", "hunt wall exceeded"
        return "counterexample", ""

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=4)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == "fail"
    assert "unadjudicated timeout" in mutants.detail
    assert "timeout_kills" in mutants.detail
    assert len(score.timeouts) == 1


def test_adjudicated_timeout_counts_as_visible_kill(tmp_path, monkeypatch):
    # With the divergence adjudicated in meta.json, the timeout is a kill,
    # visibly labeled in the passing rung.
    import json as json_mod

    from lemmapy.benchmark import runner as runner_mod
    from lemmapy.benchmark.mutate import generate_mutations

    src = "#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    first_desc = generate_mutations(src, max_mutants=4)[0][0]
    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(src)
    (task_dir / "meta.json").write_text(
        json_mod.dumps({"id": "t", "timeout_kills": [first_desc]}))
    calls = {"n": 0}

    def fake_hunt(source, name, workdir, timeout, wall=None):
        calls["n"] += 1
        if calls["n"] == 1:
            return "clean", ""
        if calls["n"] == 2:
            return "timeout", "hunt wall exceeded"
        return "counterexample", ""

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=4)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == "pass"
    assert "adjudicated timeout kill" in mutants.detail
    assert score.adjudicated_timeouts == 1
    assert score.mutants_killed == score.mutants_total


def test_mutant_descriptions_are_unique_within_a_panel():
    # The adjudication channels key on the description, so a collision
    # would let ONE human ruling apply to several mutants (a ruling about
    # an equivalent mutant could erase a real spec weakness from the
    # denominator). Descriptions carry the column for exactly this reason.
    from collections import Counter
    from pathlib import Path

    src = (
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int, c: int) -> int:\n"
        "    if a + b + c > 0:\n"
        "        return 1\n"
        "    return 0\n"
    )
    descs = [d for d, _ in generate_mutations(src, max_mutants=16)]
    assert len(descs) >= 2
    assert not [k for k, v in Counter(descs).items() if v > 1]

    # ...and across the shipped corpus, whose panels the published
    # scorecard rests on.
    tasks = Path(__file__).resolve().parent.parent / "benchmark" / "tasks"
    for task_dir in sorted(tasks.iterdir()):
        task_py = task_dir / "task.py"
        if not task_py.exists():
            continue
        panel = [d for d, _ in generate_mutations(task_py.read_text(), 8)]
        dups = [k for k, v in Counter(panel).items() if v > 1]
        assert not dups, f"{task_dir.name}: colliding descriptions {dups}"


def test_stale_or_ambiguous_adjudication_errors_the_rung(tmp_path, monkeypatch):
    # A ruling that matches no mutant is stale (a source edit shifted the
    # site) or a typo; scoring the panel anyway would publish a number
    # whose meaning is unknown.
    import json as json_mod

    from lemmapy.benchmark import runner as runner_mod

    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(
        "#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    )
    (task_dir / "meta.json").write_text(json_mod.dumps(
        {"id": "t", "timeout_kills": ["line 999 col 1: `+` -> `-`"]}))

    calls = {"n": 0}

    def fake_hunt(source, name, workdir, timeout, wall=None):
        calls["n"] += 1
        return ("clean", "") if calls["n"] == 1 else ("counterexample", "")

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=4)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == runner_mod.ERROR
    assert "matches 0 mutants" in mutants.detail
    # The panel never scored: no kills were counted despite every hunt
    # being a counterexample.
    assert score.mutants_killed == 0
    assert score.height == 2  # gate + hunt only; the panel never scored


def test_contradictory_adjudications_error_the_rung(tmp_path, monkeypatch):
    # A mutant ruled BOTH equivalent (exclude from the denominator) and a
    # timeout kill (count as killed) is a contradiction. Each entry passes
    # validation alone, and the equivalence filter would silently win,
    # dropping the mutant and overstating spec strength.
    import json as json_mod

    from lemmapy.benchmark import runner as runner_mod

    src = "#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    first = generate_mutations(src, max_mutants=4)[0][0]
    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(src)
    (task_dir / "meta.json").write_text(json_mod.dumps(
        {"id": "t", "equivalent_mutants": [first], "timeout_kills": [first]}))

    calls = {"n": 0}

    def fake_hunt(source, name, workdir, timeout, wall=None):
        calls["n"] += 1
        return ("clean", "") if calls["n"] == 1 else ("counterexample", "")

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=4)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == runner_mod.ERROR
    assert "contradictory" in mutants.detail
    assert score.adjudicated == 0  # nothing was excluded on a contradiction
    assert score.height == 2


def test_adjudication_outside_the_capped_panel_is_not_stale(tmp_path, monkeypatch):
    # --quick truncates the panel. A ruling about a mutant the truncated
    # run never hunts is OUT OF SCOPE, not stale — validating against the
    # capped panel instead of the complete one made `lemmapy benchmark
    # --quick` error on modp in CI.
    import json as json_mod

    from lemmapy.benchmark import runner as runner_mod

    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        if i < n - 1:\n"
        "            s = s + 1\n"
        "    return s\n"
    )
    full = [d for d, _ in generate_mutations(src, max_mutants=10**6)]
    assert len(full) > 2, full
    beyond_cap = full[-1]  # exists in the full panel, not in a cap-2 run

    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(src)
    (task_dir / "meta.json").write_text(json_mod.dumps(
        {"id": "t", "timeout_kills": [beyond_cap]}))

    calls = {"n": 0}

    def fake_hunt(source, name, workdir, timeout, wall=None):
        calls["n"] += 1
        return ("clean", "") if calls["n"] == 1 else ("counterexample", "")

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=2)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == "pass", mutants.detail
    assert score.mutants_total == 2


def test_panel_emptied_by_adjudication_fails_not_skips(tmp_path, monkeypatch):
    # SKIP counts toward ladder height: a panel whose every mutant was
    # ruled equivalent measured NOTHING and must not read as "no mutation
    # sites".
    import json as json_mod

    from lemmapy.benchmark import runner as runner_mod

    src = "#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    all_descs = [d for d, _ in generate_mutations(src, max_mutants=8)]
    task_dir = tmp_path / "t"
    task_dir.mkdir()
    (task_dir / "task.py").write_text(src)
    (task_dir / "meta.json").write_text(json_mod.dumps(
        {"id": "t", "equivalent_mutants": all_descs}))

    monkeypatch.setattr(runner_mod, "_hunt", lambda *a, **k: ("clean", ""))
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=8)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == "fail"
    assert "emptied by adjudication" in mutants.detail
    assert score.height == 2  # the rung blocks the climb


def test_error_census_names_timeouts_too(tmp_path, monkeypatch):
    # With an errored analysis AND an unadjudicated timeout, the printed
    # decomposition must still add up to the panel, and the remedy pointer
    # must not vanish behind the error precedence.
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
    verdicts = iter(["clean", "counterexample", "timeout", "sentinel"])

    def fake_hunt(source, name, workdir, timeout, wall=None):
        v = next(verdicts, "sentinel")
        if v == "sentinel":
            return runner_mod.ERROR, "crosshair exited 2"
        return v, ""

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True, "errors": []})())
    score = runner_mod.run_task(task_dir, tmp_path / "w", mutant_cap=3)
    mutants = next(r for r in score.rungs if r.name == "mutants")
    assert mutants.status == runner_mod.ERROR
    assert "unadjudicated timeout(s)" in mutants.detail
    assert "timeout_kills" in mutants.detail
    # killed + survivors + timeouts + errors == panel
    assert (score.mutants_killed + len(score.survivors) + len(score.timeouts)
            + 1) == score.mutants_total


def test_report_marks_and_footnotes_adjudicated_panels():
    # The headline must not pass human judgement off as measurement.
    from lemmapy.benchmark.runner import PASS, Rung, TaskScore, render_report

    s = TaskScore(task_id="t")
    s.mutants_total, s.mutants_killed = 3, 3
    s.adjudicated_timeouts = 1
    s.adjudicated = 2
    s.rungs.extend([Rung(n, PASS, "") for n in
                    ("gate", "hunt", "mutants", "encode", "prove", "fidelity")])
    report = render_report([s])
    row = next(l for l in report.splitlines() if l.startswith("t "))
    assert "3/3*" in row
    assert "human-adjudicated" in report
    assert "adjudicated equivalent" in report


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


def test_hunt_subprocess_exceptions_have_distinct_verdicts(tmp_path, monkeypatch):
    # Neither a stuck nor an unlaunchable CrossHair may abort the run:
    # wall exhaustion is its own verdict (a diverging mutant is a kill),
    # launch failure stays an analysis error.
    import subprocess as sp

    from lemmapy.benchmark import runner as runner_mod

    src = "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n"
    monkeypatch.setattr(runner_mod, "_find_crosshair", lambda: "crosshair")

    monkeypatch.setattr(runner_mod.subprocess, "run",
                        lambda cmd, **kw: (_ for _ in ()).throw(sp.TimeoutExpired(cmd, 1)))
    verdict, detail = runner_mod._hunt(src, "t", tmp_path, per_condition_timeout=1)
    assert verdict == "timeout"
    assert "wall exceeded" in detail

    monkeypatch.setattr(runner_mod.subprocess, "run",
                        lambda cmd, **kw: (_ for _ in ()).throw(OSError("boom")))
    verdict, detail = runner_mod._hunt(src, "t2", tmp_path, per_condition_timeout=1)
    assert verdict == runner_mod.ERROR
    assert "OSError" in detail


def _full_stack_available() -> bool:
    from lemmapy.backends.dafny.driver import find_dafny
    from lemmapy.benchmark.runner import _find_crosshair

    try:
        import _dafny  # noqa: F401
        import hypothesis  # noqa: F401
    except ImportError:
        return False
    return find_dafny() is not None and _find_crosshair() is not None


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


@pytest.mark.skipif(not _full_stack_available(), reason="full toolchain not installed")
def test_bump_climbs_the_full_ladder(tmp_path):
    from lemmapy.benchmark.runner import run_task

    task_dir = Path(__file__).resolve().parent.parent / "benchmark" / "tasks" / "bump"
    score = run_task(task_dir, tmp_path, mutant_cap=2, hunt_timeout=5,
                     dafny_time_limit=30, difftest_examples=15)
    assert score.height == 6, [(r.name, r.status, r.detail) for r in score.rungs]
    assert score.mutants_total >= 1
    assert score.mutants_killed == score.mutants_total
