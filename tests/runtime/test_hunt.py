"""Counterexample search distinguishes faults, timeouts and tool errors."""


def test_hunt_unwritable_workdir_degrades_to_error(tmp_path):
    # Staging failures (mkdir/write) must yield a per-item ERROR verdict,
    # not a traceback that aborts verification.
    from veripy.backends.runtime.hunt import _hunt

    blocker = tmp_path / "blocker"
    blocker.write_text("")  # a file where the workdir must be a directory
    verdict, detail = _hunt(
        "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n",
        "t", blocker / "sub", per_condition_timeout=1,
    )
    assert verdict == "error"
    assert "could not stage" in detail


def test_hunt_subprocess_exceptions_have_distinct_verdicts(tmp_path, monkeypatch):
    # Neither a stuck nor an unlaunchable CrossHair may abort the run:
    # wall exhaustion is its own verdict (a diverging mutant is a kill),
    # launch failure stays an analysis error.
    import subprocess as sp

    from veripy.backends.runtime import hunt as runner_mod

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
    assert verdict == "error"
    assert "OSError" in detail
