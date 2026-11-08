from pathlib import Path

import pytest

from veripy.cli import cmd_check
from veripy.frontend.typegate import find_basedpyright, run_type_gate

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
    # fragment=False isolates the gate behavior: the unannotated parameter
    # would (correctly) fail the fragment conformance dry-run.
    status = cmd_check([module], types=False, fragment=False)
    out = capsys.readouterr().out
    assert status == 0
    assert "type gate" not in out


def test_unavailable_gate_fails_check(tmp_path, capsys, monkeypatch):
    from veripy.frontend import typegate

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
        if "strict_proj" in d.file and d.rule != "veripy-strict-required"
    ]
    assert strict_errors
    # ...while the weak project's file fails the gate rather than being
    # checked meaninglessly under its own lax settings.
    basic_errors = [d for d in result.errors if "basic_proj" in d.file]
    assert basic_errors
    assert all(d.rule == "veripy-strict-required" for d in basic_errors)


def test_weak_config_cannot_lower_the_gate(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode": "off"}\n')
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert result.errors[0].rule == "veripy-strict-required"


def test_recommended_mode_satisfies_the_gate(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text(
        '{"typeCheckingMode": "recommended", "reportUnusedParameter": false}\n'
    )
    result = run_type_gate([module])
    assert result.available
    assert not any(d.rule == "veripy-strict-required" for d in result.errors)


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
    assert all(d.rule == "veripy-strict-required" for d in result.errors)


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


def test_extends_inheriting_weak_mode_flagged(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "base.json").write_text('{"typeCheckingMode": "basic"}\n')
    (tmp_path / "pyrightconfig.json").write_text('{"extends": "./base.json"}\n')
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert result.errors[0].rule == "veripy-strict-required"


def test_extends_inheriting_env_override_flagged(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def f(x):\n    return x + 1\n")
    (tmp_path / "base.json").write_text(
        '{"typeCheckingMode": "strict", "executionEnvironments": '
        '[{"root": ".", "reportUnknownParameterType": "none"}]}\n'
    )
    (tmp_path / "pyrightconfig.json").write_text('{"extends": "./base.json"}\n')
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert all(d.rule == "veripy-strict-required" for d in result.errors)


def test_extends_strict_base_passes(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "base.json").write_text('{"typeCheckingMode": "strict"}\n')
    (tmp_path / "pyrightconfig.json").write_text('{"extends": "./base.json"}\n')
    result = run_type_gate([module])
    assert result.available
    assert not result.errors, [d.message for d in result.errors]


def test_extends_missing_base_fails_closed(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text('{"extends": "./nope.json"}\n')
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert "unreadable" in result.errors[0].message


def test_jsonc_config_parses(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyrightconfig.json").write_text(
        '{\n'
        '  /* block comment */\n'
        '  "typeCheckingMode": "strict", // inline comment\n'
        '  "reportUnusedParameter": false,\n'
        '}\n'
    )
    result = run_type_gate([module])
    assert result.available
    assert not any(d.rule == "veripy-strict-required" for d in result.errors), [
        d.message for d in result.errors
    ]


def test_inherited_env_root_resolved_against_declaring_dir(tmp_path):
    # Base config lives in cfg/ and declares an override for root "pkg" —
    # i.e. cfg/pkg relative to the file that declared it. The gated module
    # lives exactly there; resolving only against the governing dir (tmp)
    # would miss it.
    cfg_dir = tmp_path / "cfg"
    pkg_dir = cfg_dir / "pkg"
    pkg_dir.mkdir(parents=True)
    module = pkg_dir / "m.py"
    module.write_text("def f(x):\n    return x + 1\n")
    (cfg_dir / "base.json").write_text(
        '{"typeCheckingMode": "strict", "executionEnvironments": '
        '[{"root": "pkg", "reportUnknownParameterType": "none"}]}\n'
    )
    (tmp_path / "pyrightconfig.json").write_text('{"extends": "./cfg/base.json"}\n')
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert all(d.rule == "veripy-strict-required" for d in result.errors)


def test_weak_pyproject_table_flagged(tmp_path):
    module = tmp_path / "m.py"
    module.write_text("def g(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "pyproject.toml").write_text(
        '[tool.pyright]\ntypeCheckingMode = "basic"\n'
    )
    result = run_type_gate([module])
    assert result.available
    assert result.errors
    assert result.errors[0].rule == "veripy-strict-required"


def test_checker_resolves_packages_from_current_interpreter(tmp_path):
    module = _strict_project(
        tmp_path,
        "from icontract import DBC\n\nclass Subject(DBC):\n    pass\n",
    )
    result = run_type_gate([module])
    assert result.available
    assert not result.errors, [d.message for d in result.errors]


def test_checker_uses_current_python_and_nonzero_exit_fails_closed(tmp_path, monkeypatch):
    import json
    import subprocess
    import sys
    from veripy.frontend import typegate

    commands = []

    def failed_checker(cmd, **kwargs):
        commands.append(cmd)
        return subprocess.CompletedProcess(cmd, 7, json.dumps({"generalDiagnostics": []}), "checker crashed")

    monkeypatch.setattr(typegate.subprocess, "run", failed_checker)
    module = _strict_project(tmp_path, "def g(x: int) -> int:\n    return x\n")
    result = run_type_gate([module])
    assert not result.available
    assert "7" in result.error
    command = commands[0]
    assert command[command.index("--pythonpath") + 1] == sys.executable


@pytest.mark.parametrize("payload", [
    [], {}, {"generalDiagnostics": None}, {"generalDiagnostics": [None]},
    {"version": "1.39.9", "generalDiagnostics": [], "summary": {"filesAnalyzed": 0}},
    {"version": "1.39.9", "generalDiagnostics": [{"range": None}], "summary": {"filesAnalyzed": 1}},
])
def test_incomplete_checker_output_cannot_certify_types(tmp_path, monkeypatch, payload):
    import json
    import subprocess
    from veripy.frontend import typegate

    def incomplete_checker(cmd, **kwargs):
        return subprocess.CompletedProcess(cmd, 0, json.dumps(payload), "")

    monkeypatch.setattr(typegate.subprocess, "run", incomplete_checker)
    module = _strict_project(tmp_path, "def g(x: int) -> int:\n    return x\n")
    result = run_type_gate([module])
    assert not result.available
    assert result.error


def test_complete_warning_only_checker_outcome_retains_evidence(tmp_path, monkeypatch):
    import json
    import subprocess
    from veripy.frontend import typegate

    module = _strict_project(tmp_path, "def g(x: int) -> int:\n    return x\n")
    payload = {
        "version": "1.39.9",
        "generalDiagnostics": [{"file": str(module), "severity": "warning", "message": "unused declaration", "range": {"start": {"line": 0}}}],
        "summary": {"filesAnalyzed": 1, "errorCount": 0, "warningCount": 1, "informationCount": 0},
    }

    def warning_checker(cmd, **kwargs):
        return subprocess.CompletedProcess(cmd, 1, json.dumps(payload), "")

    monkeypatch.setattr(typegate.subprocess, "run", warning_checker)
    result = run_type_gate([module])
    assert result.available, result.error
    assert not result.errors
    assert len(result.warnings) == 1
