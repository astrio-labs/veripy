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
def test_bump_climbs_the_full_ladder(tmp_path):
    from lemmapy.benchmark.runner import run_task

    task_dir = Path(__file__).resolve().parent.parent / "benchmark" / "tasks" / "bump"
    score = run_task(task_dir, tmp_path, mutant_cap=2, hunt_timeout=5,
                     dafny_time_limit=30, difftest_examples=15)
    assert score.height == 6, [(r.name, r.status, r.detail) for r in score.rungs]
    assert score.mutants_total >= 1
    assert score.mutants_killed == score.mutants_total
