"""Translation-validation harness tests (need dafny + DafnyRuntimePython)."""

from pathlib import Path

import pytest

pytest.importorskip("hypothesis")

from veripy.backends.dafny.driver import find_dafny
from veripy.difftest.harness import (
    DiffResult,
    diff_functions,
    difftest_file,
    from_dafny,
    to_dafny,
)


def _runtime_available() -> bool:
    try:
        import _dafny  # noqa: F401
        return True
    except ImportError:
        return False


pytestmark = pytest.mark.skipif(
    find_dafny() is None or not _runtime_available(),
    reason="dafny or DafnyRuntimePython not installed",
)

REPO = Path(__file__).resolve().parent.parent
EXAMPLES = REPO / "examples"


def test_value_adapter_round_trips():
    for value, tdesc in [
        (42, "int"),
        (True, "bool"),
        ("héllo", "str"),
        ("", "str"),
        ([1, -2, 3], ("list", "int")),
        ([], ("list", "int")),
        (["ab", ""], ("list", "str")),
    ]:
        assert from_dafny(to_dafny(value, tdesc), tdesc) == value


@pytest.mark.parametrize("example", ["bump.py", "clamp.py"])
def test_examples_translation_faithful(tmp_path, example):
    result = difftest_file(EXAMPLES / example, tmp_path, examples=60)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_contact_palindrome_translation_faithful(tmp_path):
    result = difftest_file(
        EXAMPLES / "contact" / "he_humaneval_48.py", tmp_path, examples=60
    )
    assert result.error is None and all(f.ok for f in result.functions)


def test_unverified_gcd_still_difftests(tmp_path):
    # Verification status is irrelevant to translation fidelity: gcd's
    # maximality proof times out, but its translation must still agree.
    result = difftest_file(
        EXAMPLES / "contact" / "he_humaneval_13.py", tmp_path, examples=60
    )
    assert result.error is None and all(f.ok for f in result.functions)


def test_keyword_only_params_difftest(tmp_path):
    src = tmp_path / "kw.py"
    src.write_text(
        "#@ requires lo <= hi\n"
        "#@ ensures lo <= result <= hi\n"
        "def clamp_kw(x: int, *, lo: int, hi: int) -> int:\n"
        "    return min(max(x, lo), hi)\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=60)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_harness_detects_divergence(tmp_path):
    # Compile bump's stub, then compare it against a WRONG original: the
    # harness must find and shrink a counterexample.
    result = difftest_file(EXAMPLES / "bump.py", tmp_path, examples=60)
    assert result.ok  # sanity: the real pairing agrees

    import ast

    source = (EXAMPLES / "bump.py").read_text()
    from veripy.difftest.harness import (
        _compiled_member,
        _load_compiled_module,
    )

    compiled_dir = tmp_path / "bump" / "compiled-py"
    compiled = _load_compiled_module(compiled_dir)
    compiled_fn = _compiled_member(compiled.default__, "bump")

    def bump_wrong(x: int) -> int:
        return x + 2

    diff = diff_functions(
        bump_wrong, compiled_fn, ["x"], ["int"], "int",
        requires_sources=[], examples=60,
    )
    assert diff.mismatch is not None
    m = diff.mismatch
    assert m.python_result == m.args[0] + 2
    assert m.dafny_result == m.args[0] + 1

# --- M1 exit criterion: the harness must CATCH a seeded encoder bug ---------------
#
# The M1 exit criteria require that the differential harness "has caught at
# least one seeded encoder bug". A statically-caught bug does not discharge
# that: it demonstrates the encoder's own checks, not the harness. This test
# injects a real miscompilation into the preamble and asserts the harness
# finds it — so the criterion is backed by an artifact CI re-runs, and if the
# harness ever stops seeing this bug class the test says so.

SEEDED_MOD = (
    "#@ requires b != 0\n"
    "def pymod(a: int, b: int) -> int:\n"
    "    return a % b\n"
)


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_difftest_catches_a_seeded_encoder_bug(tmp_path, monkeypatch):
    src = tmp_path / "seed.py"
    src.write_text(SEEDED_MOD)

    # Baseline: the real preamble models Python's floor-based `%` exactly.
    clean = difftest_file(src, tmp_path / "clean", examples=200)
    assert clean.ok, clean.error or [
        (f.name, f.mismatch, f.error) for f in clean.functions]

    # Seed the bug: collapse PyMod to Dafny's raw (Euclidean) `%`, dropping
    # the negative-divisor correction. Python: 7 % -3 == -2; Euclidean: 1.
    import veripy.backends.dafny.encoder as enc

    floor_correction = "if b < 0 && a % b != 0 then a % b + b else a % b"
    assert floor_correction in enc.PREAMBLE, "preamble PyMod shape changed"
    monkeypatch.setattr(
        enc, "PREAMBLE", enc.PREAMBLE.replace(floor_correction, "a % b"))

    seeded = difftest_file(src, tmp_path / "seeded", examples=200)
    assert not seeded.ok, "the harness did not see a seeded PyMod miscompilation"
    diff = next(f for f in seeded.functions if f.name == "pymod")
    assert diff.mismatch is not None, diff.error
    # The counterexample must be a negative divisor — the exact case the
    # dropped correction governs, not an unrelated flake.
    a, b = diff.mismatch.args
    assert b < 0, diff.mismatch
    assert diff.mismatch.python_result == a % b
    assert diff.mismatch.python_result != diff.mismatch.dafny_result
