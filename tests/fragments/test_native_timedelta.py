"""Source-bound native delay support must prove the real bodies and reject faults."""

import ast
import shutil
from pathlib import Path

import pytest
from veripy import api
from veripy.backends.base import available_backends

FIXTURE = Path(__file__).resolve().parents[2] / "case_studies/due/retry_delays.py"


def stage(tmp_path, mutation=None):
    source = FIXTURE.read_text()
    if mutation == "no-cap":
        source = source.replace(
            "        if step >= (self.maximum // self.initial).bit_length():\n            return self.maximum\n",
            "",
        )
    elif mutation == "shift":
        source = source.replace("1 << step", "1 << (step + 1)")
    elif mutation == "no-negative-guard":
        source = source.replace(
            '        if step < 0:\n            raise ValueError("delay step must be nonnegative")\n',
            "",
        )
    path = tmp_path / "delay.py"
    path.write_text(source)
    sidecar = FIXTURE.with_suffix(".proofs.dfy")
    if sidecar.exists():
        shutil.copyfile(sidecar, path.with_suffix(".proofs.dfy"))
    return path


def test_backend_is_explicit_and_does_not_replace_upstream_default():
    assert "dafny-native" in available_backends()
    assert "dafny" in available_backends() and "dafny-outcomes" in available_backends()


def test_fixture_preserves_actual_executable_method_asts():
    def bodies(path):
        tree = ast.parse(path.read_text())
        cls = next(n for n in tree.body if isinstance(n, ast.ClassDef))
        return {
            n.name: ast.dump(n, include_attributes=False)
            for n in cls.body
            if isinstance(n, ast.FunctionDef)
        }

    assert bodies(FIXTURE) == bodies(FIXTURE.with_name("original.py"))


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "mutation,expected",
    [
        (None, "ok"),
        ("no-cap", "failed"),
        ("shift", "failed"),
        ("no-negative-guard", "ok"),
    ],
)
def test_actual_bodies_and_meaningful_mutations(tmp_path, mutation, expected):
    path = stage(tmp_path, mutation)
    result = api.verify(
        path,
        tmp_path / "proof",
        backend="dafny-native",
        time_limit=20,
        keep_artifacts=True,
    )
    assert result["status"] == expected, result
    if expected == "failed":
        assert result["failures"]
        assert all(
            f["kind"] not in ("conformance", "unknown", "timeout")
            for f in result["failures"]
        )
    assert result["translation"]["source_sha256"]
    assert result["translation"]["body_ast_preserved"]
    assert result["translation"]["unit"] == "exact integer microseconds"


@pytest.mark.parametrize(
    "old,new",
    [
        ("frozen=True, slots=True", "frozen=False, slots=True"),
        ("initial: timedelta", "initial: float"),
        ("timedelta(0)", "timedelta(seconds=0.5)"),
        ("class ExponentialDelay:", "class ExponentialDelay(object):"),
        (
            "return self.initial * (1 << step)",
            "self.initial = self.maximum\n        return self.initial",
        ),
        ("return self.initial * (1 << step)", "return self.initial / 2"),
    ],
)
def test_unsupported_semantics_fail_closed(tmp_path, old, new):
    path = stage(tmp_path)
    path.write_text(path.read_text().replace(old, new))
    result = api.verify(
        path, tmp_path / "proof", backend="dafny-native", keep_artifacts=True
    )
    assert result["status"] == "encode-error", result


def test_rebinding_semantic_dependency_fails_closed(tmp_path):
    path = stage(tmp_path)
    path.write_text(path.read_text() + "\ntimedelta = int\n")
    result = api.verify(
        path, tmp_path / "proof", backend="dafny-native", keep_artifacts=True
    )
    assert result["status"] == "encode-error", result


def test_collateral_builtin_shadow_cannot_disappear_during_lowering(tmp_path):
    path = stage(tmp_path)
    path.write_text(
        path.read_text() + "\ndef min(a: int, b: int) -> int:\n    return a\n"
    )
    result = api.verify(
        path, tmp_path / "proof", backend="dafny-native", keep_artifacts=True
    )
    assert result["status"] == "encode-error", result


@pytest.mark.parametrize("name", ["min", "max", "ValueError", "bit_length"])
def test_local_semantic_bindings_are_not_treated_as_builtins(tmp_path, name):
    path = stage(tmp_path)
    source = path.read_text().replace(
        "def at(self, step: int)", f"def at(self, step: int, {name}: int)"
    )
    if name in ("min", "max"):
        source = source.replace(
            "return self.initial * (1 << step)",
            f"return {name}(self.initial, self.maximum)",
        )
    elif name == "bit_length":
        source = source.replace(
            "(self.maximum // self.initial).bit_length()",
            "bit_length(self.maximum // self.initial)",
        )
    path.write_text(source)
    result = api.verify(
        path, tmp_path / "proof", backend="dafny-native", keep_artifacts=True
    )
    assert result["status"] == "encode-error", result


@pytest.mark.parametrize("method", ["__getattribute__", "__getattr__", "__init__", "__setattr__"])
def test_special_methods_cannot_replace_native_record_semantics(tmp_path, method):
    source = f'''from dataclasses import dataclass
from datetime import timedelta
@dataclass(frozen=True)
class Sample:
    duration: timedelta
    #@ ensures not raised() and result == 0
    def {method}(self, name: int) -> int:
        return 0
    #@ ensures not raised() and result == self.duration
    def read(self) -> timedelta:
        return self.duration
'''
    path = tmp_path / "descriptor.py"
    path.write_text(source)
    result = api.verify(path, tmp_path / "proof", backend="dafny-native")
    assert result["status"] == "encode-error", result
