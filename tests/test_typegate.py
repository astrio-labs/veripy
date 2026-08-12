from pathlib import Path

import pytest

from lemmapy.cli import cmd_check
from lemmapy.frontend.typegate import find_basedpyright, run_type_gate

pytestmark = pytest.mark.skipif(
    find_basedpyright() is None, reason="basedpyright not installed"
)


def _strict_project(tmp_path: Path, source: str) -> Path:
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode": "strict"}\n')
    module = tmp_path / "m.py"
    module.write_text(source)
    return module


def test_typed_file_passes_strict(tmp_path):
    module = _strict_project(tmp_path, "def g(x: int) -> int:\n    return x + 1\n")
    result = run_type_gate([module])
    assert result.available
    assert not result.errors, [d.message for d in result.errors]


def test_untyped_function_fails_strict(tmp_path):
    module = _strict_project(tmp_path, "def f(x):\n    return x + 1\n")
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert any(d.line == 1 for d in result.errors)


def test_cli_check_gates_on_types(tmp_path, capsys):
    module = _strict_project(
        tmp_path,
        "#@ ensures result >= 0 or result < 0\ndef f(x):\n    return x\n",
    )
    status = cmd_check([module], types=True)
    out = capsys.readouterr().out
    assert status == 1
    assert "type gate (basedpyright" in out


def test_cli_no_types_skips_gate(tmp_path, capsys):
    module = _strict_project(
        tmp_path,
        "#@ ensures result >= 0 or result < 0\ndef f(x):\n    return x\n",
    )
    status = cmd_check([module], types=False)
    out = capsys.readouterr().out
    assert status == 0
    assert "type gate" not in out
