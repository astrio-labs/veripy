from pathlib import Path

import pytest

from veripy.benchmark.mutate import generate_mutations

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


def test_operand_replacement_swaps_same_typed_parameters():
    """The family that gives the rung resolution.

    Every other family perturbs an OPERATOR, so a specification that never
    says which input the result depends on scores full marks. `clamp` was
    the corpus's own counterexample: with the weaker "result is one of x,
    lo, hi" postcondition — satisfied by `return lo`, ignoring the input —
    it scored identically to a spec that determines the function.
    """
    descriptions = [d for d, _ in generate_mutations(CLAMP, max_mutants=16)]
    joined = " | ".join(descriptions)
    assert "`x` -> `lo`" in joined
    assert "`lo` -> `hi`" in joined
    # Sources stay parseable and specs untouched.
    for _d, mutated in generate_mutations(CLAMP, max_mutants=16):
        import ast

        ast.parse(mutated)
        assert "#@ ensures" in mutated


def test_operand_replacement_respects_types_and_scope():
    # Only same-annotation parameters are swapped: a cross-type swap would
    # raise TypeError and a non-parameter name could raise NameError —
    # either way the "fault" would be caught by the interpreter rather than
    # discriminated by the spec, wasting a panel slot.
    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int, xs: list[int], m: int) -> int:\n"
        "    total = n + m\n"
        "    return total\n"
    )
    joined = " | ".join(d for d, _ in generate_mutations(src, max_mutants=16))
    assert "`n` -> `m`" in joined and "`m` -> `n`" in joined
    assert "xs" not in joined      # different annotation
    assert "total" not in joined   # a local, not a parameter — and only
                                   # READ sites are mutation sites


def test_panel_cap_is_round_robin_not_a_line_prefix():
    # A positional cap makes the panel a line-prefix of the function, so a
    # later family (or the back half of the body) goes silently unprobed.
    src = (
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    t = a + 1\n"
        "    t = t + a\n"
        "    t = t + a\n"
        "    if a < b:\n"
        "        t = t + b\n"
        "    return t\n"
    )
    capped = [d for d, _ in generate_mutations(src, max_mutants=4)]
    assert len(capped) == 4
    # Both families survive the cap.
    assert any("`a` -> `b`" in d or "`b` -> `a`" in d for d in capped), capped
    assert any("->" in d and ("`+`" in d or "`<`" in d or "`1`" in d)
               for d in capped), capped
    # And selection stays deterministic.
    assert capped == [d for d, _ in generate_mutations(src, max_mutants=4)]


def test_errored_mutant_analysis_blocks_the_rung(tmp_path, monkeypatch):
    # An incomplete panel (analysis errors) must not read as passing.
    from veripy.benchmark import runner as runner_mod

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
    from veripy.benchmark import runner as runner_mod

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
    from veripy.benchmark import runner as runner_mod

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
    from veripy.benchmark import runner as runner_mod

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


def test_adjudicated_timeout_passes_the_rung_without_being_credited(
        tmp_path, monkeypatch):
    """Adjudicated divergence: does not FAIL the rung, does not COUNT as
    spec strength.

    This test previously asserted the timeout was a kill
    (`mutants_killed == mutants_total`). That was the same hole crediting
    crashes had: the hunt wall expires on a diverging mutant whatever the
    specification says, so `#@ ensures True` "kills" it equally and the
    mutant carries no information about the spec. The human ruling
    establishes a behaviour change — which is why the rung still passes —
    not that the spec discriminated it.
    """
    import json as json_mod

    from veripy.benchmark import runner as runner_mod
    from veripy.benchmark.mutate import generate_mutations

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
    assert "diverged" in mutants.detail and "not credited" in mutants.detail
    assert score.adjudicated_timeouts == [first_desc]
    assert score.mutants_killed == score.mutants_total - 1
    # Adjudicated or not, the wall was exhausted: both channels are the
    # arm's inconclusive hunts, and the spec exam compares them by NAME
    # across arms, so a ruled timeout may not drop out of the record.
    assert score.timeout_mutants == [first_desc]


def test_timeout_mutants_names_both_channels():
    from veripy.benchmark.runner import TaskScore

    score = TaskScore(task_id="t")
    assert score.timeout_mutants == []
    score.timeouts = ["line 1 col 2: `+` -> `-`"]
    score.adjudicated_timeouts = ["line 4 col 9: `<` -> `<=`"]
    assert score.timeout_mutants == ["line 1 col 2: `+` -> `-`",
                                     "line 4 col 9: `<` -> `<=`"]


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

    from veripy.benchmark import runner as runner_mod

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

    from veripy.benchmark import runner as runner_mod

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
    # capped panel instead of the complete one made `veripy benchmark
    # --quick` error on modp in CI.
    import json as json_mod

    from veripy.benchmark import runner as runner_mod

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

    from veripy.benchmark import runner as runner_mod

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
    from veripy.benchmark import runner as runner_mod

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
    from veripy.benchmark.runner import PASS, Rung, TaskScore, render_report

    s = TaskScore(task_id="t")
    s.mutants_total, s.mutants_killed = 3, 3
    s.adjudicated_timeouts = ["line 3 col 7: `<` -> `<=`"]
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
    from veripy.benchmark.runner import ERROR, FAIL, PASS, Rung, TaskScore, render_report

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
    from veripy.benchmark.runner import ERROR, _hunt

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
    from veripy.benchmark.runner import ERROR, run_benchmark

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

    from veripy.benchmark import runner as runner_mod

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
    from veripy.backends.dafny.driver import find_dafny
    from veripy.benchmark.runner import _find_crosshair

    try:
        import _dafny  # noqa: F401
        import hypothesis  # noqa: F401
    except ImportError:
        return False
    return find_dafny() is not None and _find_crosshair() is not None


def test_cmd_benchmark_exit_status_mirrors_scorecard(tmp_path, monkeypatch):
    # CI gates on the exit code: 0 all-pass, 1 failed rungs, 2 tool errors.
    import veripy.cli as cli
    from veripy.benchmark.runner import ERROR, FAIL, PASS, Rung, TaskScore

    def score(status):
        s = TaskScore(task_id="t")
        s.rungs.append(Rung("gate", status, ""))
        return s

    for status, expected in ((PASS, 0), (FAIL, 1), (ERROR, 2)):
        monkeypatch.setattr(
            "veripy.benchmark.runner.run_benchmark",
            lambda tasks, outdir, _s=status, **kw: [score(_s)],
        )
        got = cli.cmd_benchmark(tmp_path, tmp_path / "w", report=None,
                                mutant_cap=8, quick=False)
        assert got == expected, f"{status}: expected exit {expected}, got {got}"


@pytest.mark.skipif(not _full_stack_available(), reason="full toolchain not installed")
def test_bump_climbs_the_full_ladder(tmp_path):
    from veripy.benchmark.runner import run_task

    task_dir = Path(__file__).resolve().parent.parent / "benchmark" / "tasks" / "bump"
    score = run_task(task_dir, tmp_path, mutant_cap=2, hunt_timeout=5,
                     dafny_time_limit=30, difftest_examples=15)
    assert score.height == 6, [(r.name, r.status, r.detail) for r in score.rungs]
    assert score.mutants_total >= 1
    assert score.mutants_killed == score.mutants_total


def test_thin_panels_are_marked_not_presented_as_comparable():
    """A rate over one mutant is one bit; it must not read like 8/8.

    Small panels are a real limit of mutation-based scoring on short
    functions. They still pool into the corpus total, but the per-task cell
    is marked so a reader does not compare `1/1` with `8/8` as equals.
    """
    from veripy.benchmark.runner import (
        LOW_RESOLUTION_PANEL,
        PASS,
        Rung,
        TaskScore,
        render_report,
    )

    def scored(task_id, killed, total):
        s = TaskScore(task_id=task_id)
        s.rungs = [Rung(n, PASS) for n in
                   ["gate", "hunt", "mutants", "encode", "prove", "fidelity"]]
        s.mutants_killed, s.mutants_total = killed, total
        return s

    thin, thick = scored("thin", 1, 1), scored("thick", 8, 8)
    report = render_report([thin, thick])
    assert "1/1?" in report, "a one-mutant panel must be marked"
    assert "8/8?" not in report and "8/8" in report
    assert LOW_RESOLUTION_PANEL == 3

    # The profile must report the median it computed. `[1, 8]` has median
    # 4.5, and a `.0f` format rounded it to "4" — an inaccurate statistic
    # inside the line whose whole job is to state the instrument's
    # precision. (Banker's rounding makes it read LOW, understating the
    # resolution rather than overstating it, which is the less obvious
    # direction to notice.)
    assert "median 4.5" in report, report
    assert "min 1" in report and "max 8" in report
    assert "1 task(s) marked ?" in report

    # A whole-number median must not gain a spurious decimal.
    even = render_report([scored("a", 4, 4), scored("b", 4, 4)])
    assert "median 4 " in even, even

def test_adjudicated_timeout_is_not_credited_as_spec_strength(tmp_path,
                                                              monkeypatch):
    """Divergence is caught by the wall, not by the specification.

    A human ruling that a mutant diverges establishes a real behaviour
    change, so it must not FAIL the rung. But it is not evidence the spec
    discriminated anything — the hunt wall expires the same way under
    `#@ ensures True` — so crediting it to `mutants_killed` would reopen
    exactly the hole that crediting crashes did.
    """
    import veripy.benchmark.runner as runner_mod
    from veripy.benchmark.runner import PASS, run_task

    src = ("#@ ensures result >= 0\n"
           "def f(n: int) -> int:\n"
           "    if n < 0:\n"
           "        return 0\n"
           "    return n\n")
    d = tmp_path / "t"
    d.mkdir()
    (d / "task.py").write_text(src)
    panel = [desc for desc, _ in generate_mutations(src, max_mutants=12)]
    assert panel, "need a panel to adjudicate against"
    import json as json_mod

    (d / "meta.json").write_text(json_mod.dumps(
        {"id": "t", "timeout_kills": [panel[0]]}))

    # Gate/hunt clean; the adjudicated mutant times out, the rest refute.
    monkeypatch.setattr(runner_mod, "run_type_gate",
                        lambda paths: type("G", (), {"available": True,
                                                     "errors": [],
                                                     "error": None})())
    calls = {"n": 0}

    def fake_hunt(source, name, workdir, per_condition_timeout, wall=None):
        if name == "t":
            return "clean", ""            # R1 on the original
        calls["n"] += 1
        if calls["n"] == 1:
            return "timeout", "wall exceeded"
        return "counterexample", "false when calling f(...)"

    monkeypatch.setattr(runner_mod, "_hunt", fake_hunt)
    score = run_task(d, tmp_path / "w", mutant_cap=12)

    rung = next(r for r in score.rungs if r.name == "mutants")
    assert rung.status == PASS, f"adjudicated divergence must not fail: {rung.detail}"
    assert score.adjudicated_timeouts == [panel[0]]
    # The refuted count excludes it, and the buckets still add up.
    assert score.mutants_killed == score.mutants_total - 1
    assert (score.mutants_killed + score.mutants_crashed
            + len(score.adjudicated_timeouts) + len(score.survivors)
            + len(score.timeouts)) == score.mutants_total
    assert "diverged" in rung.detail and "not credited" in rung.detail


# --- P4 phase 2: triple adjudication ---------------------------------------

def test_cross_report_reads_three_ways():
    from veripy.benchmark.runner import (ERROR, FAIL, PASS, Rung,
                                         TaskScore, render_cross_report)

    def score(task, **rungs):
        sc = TaskScore(task_id=task)
        for name, status in rungs.items():
            sc.rungs.append(Rung(name, status))
        return sc

    by_backend = {
        "dafny": [
            score("both_prove", hunt=PASS, mutants=PASS, encode=PASS,
                  prove=PASS, fidelity=PASS),
            score("lean_gap", hunt=PASS, mutants=PASS, encode=PASS,
                  prove=PASS, fidelity=PASS),
            score("alarm", hunt=PASS, mutants=PASS, encode=PASS,
                  prove=PASS, fidelity=PASS),
        ],
        "lean": [
            score("both_prove", hunt=PASS, mutants=PASS, encode=PASS,
                  prove=PASS, fidelity=PASS),
            # A refused encode is a NAMED fragment gap, not a failure.
            score("lean_gap", hunt=PASS, mutants=PASS, encode=FAIL),
            # Proved under one prover, failed under the other, neither
            # outside its fragment: a completeness gap, named out loud
            # (an alarm would need contradictory proofs, not a proof
            # beside a failure).
            score("alarm", hunt=PASS, mutants=PASS, encode=PASS,
                  prove=FAIL, fidelity=PASS),
        ],
    }
    # An errored cell must not vanish from the totals (review-caught):
    # it observed nothing, and gets its own count.
    by_backend["dafny"].append(
        score("errored", hunt=PASS, mutants=PASS, encode=PASS,
              prove=ERROR))
    by_backend["lean"].append(
        score("errored", hunt=PASS, mutants=PASS, encode=PASS,
              prove=PASS, fidelity=PASS))
    out = render_cross_report(by_backend)
    lines = {ln.split()[0]: ln for ln in out.splitlines() if ln}
    assert "proved" in lines["both_prove"]
    assert "outside" in lines["lean_gap"]
    assert "failed" in lines["alarm"]
    assert "error" in lines["errored"]
    assert "1 task(s) proved under EVERY backend" in out
    assert "1 unadjudicated" in out
    assert "COMPLETENESS" in out


def test_benchmark_backend_all_runs_every_backend(monkeypatch, tmp_path):
    # `--backend all` dispatches one ladder per registered backend and
    # exits 0 on FAILs (a measurement, not a gate) — only tool errors
    # fail the run.
    from veripy import cli as cli_mod
    from veripy.benchmark.runner import PASS, FAIL, Rung, TaskScore

    calls = []

    def fake_run_benchmark(tasks, outdir, backend="dafny", **kwargs):
        calls.append(backend)
        sc = TaskScore(task_id="t")
        sc.rungs.append(Rung("hunt", PASS))
        sc.rungs.append(Rung("prove", PASS if backend == "dafny" else FAIL))
        return [sc]

    import veripy.benchmark.runner as runner_mod
    monkeypatch.setattr(runner_mod, "run_benchmark", fake_run_benchmark)
    rc = cli_mod.cmd_benchmark(tmp_path, tmp_path / "out", None,
                               mutant_cap=3, quick=True, backend="all")
    from veripy.backends.base import available_backends
    assert calls == available_backends()
    assert rc == 0
