from pathlib import Path

import pytest

from lemmapy.cli import _find_crosshair, cmd_hunt

pytestmark = pytest.mark.skipif(
    _find_crosshair() is None, reason="crosshair not installed"
)

EXAMPLES = Path(__file__).resolve().parent.parent / "examples"


def test_hunt_finds_seeded_bug(tmp_path, capsys):
    status = cmd_hunt([EXAMPLES / "clamp.py"], tmp_path, per_condition_timeout=20)
    out = capsys.readouterr().out
    assert status == 1
    assert "COUNTEREXAMPLE" in out


def test_hunt_clean_on_correct_function(tmp_path, capsys):
    status = cmd_hunt([EXAMPLES / "bump.py"], tmp_path, per_condition_timeout=20)
    out = capsys.readouterr().out
    assert status == 0
    assert "no counterexamples" in out


def test_hunt_crosshair_error_is_not_a_counterexample(tmp_path, capsys, monkeypatch):
    import subprocess

    from lemmapy import cli

    def fake_run(cmd, **kwargs):
        return subprocess.CompletedProcess(cmd, 2, stdout="", stderr="ImportError: boom")

    monkeypatch.setattr(cli.subprocess, "run", fake_run)
    status = cmd_hunt([EXAMPLES / "bump.py"], tmp_path, per_condition_timeout=5)
    captured = capsys.readouterr()
    assert status == 2
    assert "COUNTEREXAMPLE" not in captured.out
    assert "exited 2" in captured.err


def test_emit_rejects_same_stem_inputs(tmp_path, capsys):
    from lemmapy.cli import cmd_emit

    a = tmp_path / "a"
    b = tmp_path / "b"
    a.mkdir()
    b.mkdir()
    src = "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n"
    (a / "foo.py").write_text(src)
    (b / "foo.py").write_text(src)
    status = cmd_emit([a / "foo.py", b / "foo.py"], tmp_path / "out")
    err = capsys.readouterr().err
    assert status == 1
    assert "collision" in err
    assert not (tmp_path / "out" / "foo_checked.py").exists()
