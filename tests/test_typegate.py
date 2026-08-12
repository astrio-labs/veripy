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


def test_unavailable_gate_fails_check(tmp_path, capsys, monkeypatch):
    from lemmapy.frontend import typegate

    monkeypatch.setattr(typegate, "find_basedpyright", lambda: None)
    module = _strict_project(tmp_path, "def g(x: int) -> int:\n    return x\n")
    status = cmd_check([module], types=True)
    captured = capsys.readouterr()
    assert status == 1
    assert "FAILED to run" in captured.err


def test_files_from_different_projects_use_own_configs(tmp_path):
    untyped = "def f(x):\n    return x + 1\n"
    strict_dir = tmp_path / "strict_proj"
    basic_dir = tmp_path / "basic_proj"
    strict_dir.mkdir()
    basic_dir.mkdir()
    (strict_dir / "pyrightconfig.json").write_text('{"typeCheckingMode": "strict"}\n')
    (basic_dir / "pyrightconfig.json").write_text('{"typeCheckingMode": "basic"}\n')
    (strict_dir / "m.py").write_text(untyped)
    (basic_dir / "m.py").write_text(untyped)

    result = run_type_gate([strict_dir / "m.py", basic_dir / "m.py"])
    assert result.available
    error_files = {d.file for d in result.errors}
    assert any("strict_proj" in f for f in error_files)
    assert not any("basic_proj" in f for f in error_files)
