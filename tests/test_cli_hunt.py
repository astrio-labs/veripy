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
