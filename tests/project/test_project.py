"""Exercise project verification with current source and the real proof backend."""
import json
from pathlib import Path

import pytest

from veripy.project import run_project

SOURCE = '''#@ requires n >= 0
#@ ensures result == n
def tally(n: int) -> int:
    total = 0
    for _i in range(n):
        #@ invariant total == _i
        total += 1
    return total
'''


def project(tmp_path):
    (tmp_path / "core.py").write_text(SOURCE)
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode":"strict"}')
    manifest = {
        "version": 1, "sources": ["*.py"], "required_targets": ["core"],
        "targets": [{"id": "core", "source": "core.py", "backend": "dafny",
                     "functions": ["tally"], "dependencies": []}],
        "artifacts": "proofs/generated", "dafny_version": "4.11.0",
    }
    path = tmp_path / "veripy-project.json"
    path.write_text(json.dumps(manifest))
    return path


@pytest.mark.requires_prover("dafny")
def test_current_source_regeneration_and_mutation(tmp_path):
    manifest = project(tmp_path)
    result = run_project(manifest, "generate")
    assert result["status"] == "verified", result
    artifacts = {p.name: p.read_bytes() for p in (tmp_path / "proofs/generated").iterdir()}
    assert run_project(manifest, "check")["status"] == "verified"
    assert run_project(manifest, "generate")["status"] == "verified"
    assert artifacts == {p.name: p.read_bytes() for p in (tmp_path / "proofs/generated").iterdir()}
    source = tmp_path / "core.py"
    source.write_text(SOURCE.replace("total += 1", "total = total + 1"))
    result = run_project(manifest, "check")
    assert result["status"] == "stale" and result["targets"][0]["proof_status"] == "verified", result
    assert run_project(manifest, "generate")["status"] == "verified"
    source.write_text(SOURCE.replace("total += 1", "total += 2"))
    result = run_project(manifest, "check")
    assert result["status"] == "failed", result
    assert result["targets"][0]["diagnostics"][0]["file"] == "core.py"
    assert result["targets"][0]["diagnostics"][0]["line"]


@pytest.mark.parametrize("change", ["empty", "duplicate", "missing-id", "omitted", "functions", "sources"])
def test_enrollment_cannot_silently_shrink(tmp_path, change):
    path = project(tmp_path)
    manifest = json.loads(path.read_text())
    if change == "empty":
        manifest["targets"] = []
        manifest["required_targets"] = []
    elif change == "duplicate":
        manifest["targets"] *= 2
    elif change == "missing-id":
        del manifest["targets"][0]["id"]
    elif change == "omitted":
        manifest["required_targets"].append("lost")
    elif change == "functions":
        manifest["targets"][0]["functions"] = []
    else:
        manifest["sources"] = []
    path.write_text(json.dumps(manifest))
    assert run_project(path, "check")["status"] == "enrollment-error"


@pytest.mark.requires_prover("dafny")
def test_sidecar_checked_preserved_and_contract_reviewed(tmp_path):
    path = project(tmp_path)
    sidecar = tmp_path / "core.proofs.dfy"
    original = "lemma Arithmetic(x: int)\n  ensures x + 0 == x\n{}\n"
    sidecar.write_text(original)
    manifest = json.loads(path.read_text())
    manifest["targets"][0]["sidecar"] = sidecar.name
    path.write_text(json.dumps(manifest))
    assert run_project(path, "generate")["status"] == "verified"
    assert sidecar.read_text() == original
    sidecar.write_text(original.replace("x + 0 == x", "x + 1 == x"))
    result = run_project(path, "check")
    assert result["status"] == "failed", result
    assert any(d["file"] == sidecar.name and d["line"] == 2
               for d in result["targets"][0]["diagnostics"])
    sidecar.write_text(original + "\n// proof maintenance\n")
    result = run_project(path, "generate")
    assert result["status"] == "contract-change", result
    assert run_project(path, "generate", update_contracts=True)["status"] == "verified"
    source = tmp_path / "core.py"
    source.write_text(SOURCE.replace("result == n", "True"))
    assert run_project(path, "generate")["status"] == "contract-change"
    sidecar.write_text("lemma Unsound() ensures false { assume false; }\n")
    assert run_project(path, "generate", update_contracts=True)["status"] == "unsupported"


@pytest.mark.requires_prover("dafny")
def test_discovery_dependencies_and_artifact_drift(tmp_path):
    path = project(tmp_path)
    dep = tmp_path / "policy.txt"
    dep.write_text("external semantic contract v1\n")
    manifest = json.loads(path.read_text())
    manifest["targets"][0]["dependencies"] = [dep.name]
    path.write_text(json.dumps(manifest))
    assert run_project(path, "generate")["status"] == "verified"
    dep.write_text("external semantic contract v2\n")
    assert run_project(path, "check")["status"] == "stale"
    assert run_project(path, "generate")["status"] == "verified"
    artifact = tmp_path / "proofs/generated/core.dfy"
    artifact.write_text(artifact.read_text() + "// stale edit\n")
    assert run_project(path, "check")["status"] == "stale"
    (tmp_path / "forgotten.py").write_text(SOURCE)
    assert run_project(path, "check")["status"] == "enrollment-error"


def test_missing_sidecar_and_unsupported_source_fail_explicitly(tmp_path):
    path = project(tmp_path)
    manifest = json.loads(path.read_text())
    manifest["targets"][0]["sidecar"] = "core.proofs.dfy"
    path.write_text(json.dumps(manifest))
    assert run_project(path, "check")["status"] == "enrollment-error"


@pytest.mark.requires_prover("dafny")
def test_contracts_remain_bound_to_the_enrolled_function(tmp_path):
    path = project(tmp_path)
    source = '''#@ ensures result == x
def echo(x: int) -> int:
    return x
#@ ensures result == 0
def zero(_x: int) -> int:
    return 0
'''
    module = tmp_path / "core.py"
    module.write_text(source)
    manifest = json.loads(path.read_text())
    manifest["targets"][0]["functions"] = ["echo", "zero"]
    path.write_text(json.dumps(manifest))
    assert run_project(path, "generate")["status"] == "verified"
    swapped = source.replace("def echo(", "def temporary(").replace("def zero(", "def echo(").replace("def temporary(", "def zero(")
    module.write_text(swapped)
    result = run_project(path, "generate")
    assert result["status"] == "contract-change", result


def test_generated_outputs_cannot_overwrite_declared_inputs(tmp_path):
    path = project(tmp_path)
    dependency = tmp_path / "proofs/generated/core.dfy"
    dependency.parent.mkdir(parents=True)
    dependency.write_text("reviewed external definition\n")
    manifest = json.loads(path.read_text())
    manifest["targets"][0]["dependencies"] = ["proofs/generated/core.dfy"]
    path.write_text(json.dumps(manifest))
    result = run_project(path, "generate")
    assert result["status"] == "enrollment-error", result
    assert dependency.read_text() == "reviewed external definition\n"


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize("changed,content,shared", [
    ("core.py", SOURCE.replace("total += 1", "total += 2"), False),
    ("veripy-project.json", None, False),
    # core.py is also a later target's dependency, whose re-read must not
    # replace the hash of the snapshot that was proved.
    ("core.py", SOURCE.replace("total += 1", "total += 2"), True),
])
def test_input_saved_while_loading_cannot_be_locked_as_proved(tmp_path, monkeypatch, changed, content, shared):
    """An editor save between the proof's read and the lock's hash is stale."""
    import veripy.project as project_module

    path = project(tmp_path)
    if shared:
        (tmp_path / "other.py").write_text(SOURCE)
        manifest = json.loads(path.read_text())
        manifest["required_targets"].append("other")
        manifest["targets"].append({"id": "other", "source": "other.py", "backend": "dafny",
                                    "functions": ["tally"], "dependencies": ["core.py"]})
        path.write_text(json.dumps(manifest))
    original = project_module.parse_source
    saved = []

    def parse_then_save(*args, **kwargs):
        specs = original(*args, **kwargs)
        if not saved:
            target = tmp_path / changed
            target.write_text(content if content is not None else target.read_text() + "\n")
            saved.append(changed)
        return specs

    monkeypatch.setattr(project_module, "parse_source", parse_then_save)
    result = run_project(path, "generate")
    assert saved and result["status"] == "stale", result
    assert not (tmp_path / "proofs/generated/project.lock.json").exists()


@pytest.mark.requires_prover("dafny")
def test_type_policy_drift_requires_review_and_fresh_artifacts(tmp_path):
    path = project(tmp_path)
    assert run_project(path, "generate")["status"] == "verified"
    config = tmp_path / "pyrightconfig.json"
    config.write_text('{"typeCheckingMode":"strict","reportUnusedVariable":"warning"}')
    assert run_project(path, "check")["status"] == "stale"
    result = run_project(path, "generate")
    assert result["status"] == "contract-change", result
    assert result["contract_changes"]
    assert run_project(path, "generate", update_contracts=True)["status"] == "verified"
