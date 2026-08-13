"""Verification report (§5) and island-integrity hardening."""

import importlib.util
import json
import sys
from pathlib import Path

import pytest

from lemmapy.cli import cmd_guard, cmd_verify
from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.guards.emitter import GuardGenError, emit_guarded
from lemmapy.frontend.extract import parse_source
from lemmapy.guards.runtime import IslandIntegrityError, verify_island_integrity

BUMP = (
    "#@ verified\n"
    "#@ ensures result == x + 1\n"
    "def bump(x: int) -> int:\n"
    "    return x + 1\n"
)


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


# ---- verification report ------------------------------------------------------


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_report_written_with_verdicts_and_assumptions(tmp_path, capsys):
    src = tmp_path / "m.py"
    src.write_text(BUMP)
    report = tmp_path / "report.json"
    status = cmd_verify([src], tmp_path / "out", time_limit=30, types=False,
                        report=report)
    assert status == 0
    payload = json.loads(report.read_text())
    assert payload["schema"] == "lemmapy-verification-report/1"
    assert payload["summary"] == {
        "functions": 1, "verified": 1, "failed": 0, "errors": 0,
        "trusted_contracts": 0,
    }
    fn = payload["functions"][0]
    assert fn["name"] == "bump" and fn["status"] == "verified"
    assert fn["marked_verified"] is True
    assert fn["ensures"] == ["result == x + 1"]
    assert fn["assumed_clauses"] == []  # every requires is executable
    assert [a["id"] for a in payload["assumptions"]] == [
        "A1", "A2", "A3", "A4", "A5", "A6", "A7"]
    out = capsys.readouterr().out
    assert "verified modulo 0 trusted contracts" in out


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_report_attributes_failures_to_the_failing_function(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(
        BUMP
        + "\n\n#@ ensures result == x - 1\n"
        "def broken(x: int) -> int:\n"
        "    return x + 1\n"
    )
    report = tmp_path / "report.json"
    status = cmd_verify([src], tmp_path / "out", time_limit=30, types=False,
                        report=report)
    assert status == 1
    by_name = {f["name"]: f for f in json.loads(report.read_text())["functions"]}
    assert by_name["bump"]["status"] == "verified"
    assert by_name["broken"]["status"] == "failed"
    assert by_name["broken"]["failures"]


def test_report_records_encode_errors_without_dafny(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return len(set(xs))\n"
    )
    report = tmp_path / "report.json"
    status = cmd_verify([src], tmp_path / "out", time_limit=30, types=False,
                        report=report)
    assert status == 2
    payload = json.loads(report.read_text())
    assert payload["functions"][0]["status"] == "error"
    assert payload["summary"]["errors"] == 1


# ---- island integrity ---------------------------------------------------------


def test_island_digest_verifies_and_detects_tampering(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(BUMP)
    outdir = tmp_path / "g"
    assert cmd_guard([src], outdir) == 0
    guarded = outdir / "m_guarded.py"
    digest = verify_island_integrity(guarded)
    assert len(digest) == 64
    tampered = guarded.read_text().replace("return x + 1", "return x + 2", 1)
    guarded.write_text(tampered)
    with pytest.raises(IslandIntegrityError, match="digest mismatch"):
        verify_island_integrity(guarded)


def test_rebinding_module_attributes_cannot_redirect_wrapper(tmp_path):
    # Definition-time closure binding: patching the guarded module's island
    # alias or helper attributes after import does not change what an
    # already-defined wrapper runs.
    src = tmp_path / "m.py"
    src.write_text(BUMP)
    outdir = tmp_path / "g"
    assert cmd_guard([src], outdir) == 0
    mod = _load(outdir / "m_guarded.py", "harden_m")
    assert mod.bump(1) == 2
    mod._lemmapy_island_bump = lambda x: -999
    assert mod.bump(1) == 2  # closure still runs the real island
    mod._lemmapy_guard_value = lambda v, d, **k: v  # disable checks? no:
    with pytest.raises(Exception):
        mod.bump("not an int")  # the bound guard still checks


def test_specs_cannot_reach_generated_identifiers():
    # A spec referencing a generated name is closed off twice over: the
    # frontend rejects unknown names, and making the name known (module
    # binding) trips the reserved-name scan.
    unknown = (
        "#@ requires _lemmapy_bound_guard != 0\n"
        "#@ ensures result >= 0\n"
        "def f(x: int) -> int:\n"
        "    return 0\n"
    )
    specs = parse_source(unknown)
    assert any("unknown name" in (c.error or "") for c in specs.errors)

    known = "_lemmapy_bound_guard = 1\n" + unknown
    with pytest.raises(GuardGenError, match="reserved for generated"):
        emit_guarded(known, parse_source(known), src_name="m.py")
