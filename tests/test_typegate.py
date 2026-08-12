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
    # The strict project's file is actually type-checked...
    strict_errors = [
        d for d in result.errors
        if "strict_proj" in d.file and d.rule != "lemmapy-strict-required"
    ]
    assert strict_errors
    # ...while the weak project's file fails the gate rather than being
    # checked meaninglessly under its own lax settings.
    basic_errors = [d for d in result.errors if "basic_proj" in d.file]
    assert basic_errors
    assert all(d.rule == "lemmapy-strict-required" for d in basic_errors)


def test_weak_config_cannot_lower_the_gate(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode": "off"}\n')
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert result.errors[0].rule == "lemmapy-strict-required"


def test_recommended_mode_satisfies_the_gate(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text(
        '{"typeCheckingMode": "recommended", "reportUnusedParameter": false}\n'
    )
    result = run_type_gate([module])
    assert result.available
    assert not any(d.rule == "lemmapy-strict-required" for d in result.errors)


def test_execution_environment_diagnostic_override_flagged(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def f(x):\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text(
        '{"typeCheckingMode": "strict", "executionEnvironments": '
        '[{"root": ".", "reportUnknownParameterType": "none"}]}\n'
    )
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert all(d.rule == "lemmapy-strict-required" for d in result.errors)


def test_structural_execution_environment_allowed(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text(
        '{"typeCheckingMode": "strict", "executionEnvironments": '
        '[{"root": ".", "pythonVersion": "3.12"}]}\n'
    )
    result = run_type_gate([module])
    assert result.available
    assert not result.errors, [d.message for d in result.errors]


def test_weak_pyproject_table_flagged(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyproject.toml").write_text(
        '[tool.pyright]\ntypeCheckingMode = "basic"\n'
    )
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert result.errors[0].rule == "lemmapy-strict-required"
