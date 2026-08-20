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
    type_descriptor,
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


def test_break_and_continue_translation_faithful(tmp_path):
    src = tmp_path / "ctrl.py"
    src.write_text(
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def cap10(n: int) -> int:\n"
        "    i = 0\n"
        "    while i < n:\n"
        "        #@ invariant 0 <= i <= n\n"
        "        #@ decreases n - i\n"
        "        if i == 10:\n"
        "            break\n"
        "        i = i + 1\n"
        "    return i\n"
        "\n"
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def skip_evens(n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        #@ invariant 0 <= i <= n\n"
        "        #@ invariant s >= 0\n"
        "        if i % 2 == 0:\n"
        "            continue\n"
        "        s = s + 1\n"
        "    return s\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=80)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_tuple_translation_faithful(tmp_path):
    src = tmp_path / "pair.py"
    src.write_text(
        "#@ ensures result[0] == x\n"
        "#@ ensures result[1] == y\n"
        "def pair(x: int, y: int) -> tuple[int, int]:\n"
        "    return (x, y)\n"
        "\n"
        "#@ ensures result == p[0] + p[1]\n"
        "def add_pair(p: tuple[int, int]) -> int:\n"
        "    a, b = p\n"
        "    return a + b\n"
        "\n"
        "#@ ensures result == p[-1]\n"
        "def last(p: tuple[int, bool]) -> bool:\n"
        "    return p[-1]\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=80)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_tuple_value_adapter_round_trips():
    tdesc = ("tuple", "int", "bool")
    value = (7, True)
    assert from_dafny(to_dafny(value, tdesc), tdesc) == value


def test_optional_in_tuple_type_descriptor():
    import ast

    tree = ast.parse(
        "def f(p: tuple[int | None, int]) -> tuple[int | None, int]:\n"
        "    return p\n"
    )
    fn = tree.body[0]
    assert type_descriptor(fn.args.args[0].annotation) == (
        "tuple", ("opt", "int"), "int"
    )
    assert type_descriptor(fn.returns) == ("tuple", ("opt", "int"), "int")


def test_optional_from_dafny_projects_pynone_and_pysome():
    class None_:
        is_PyNone = True

    class Some:
        def __init__(self, v):
            self.v = v
            self.is_PyNone = False

    assert from_dafny(None_(), ("opt", "int")) is None
    assert from_dafny(Some(3), ("opt", "int")) == 3
    assert from_dafny((None_(), 1), ("tuple", ("opt", "int"), "int")) == (None, 1)


def test_optional_tuple_translation_faithful(tmp_path):
    src = tmp_path / "optpair.py"
    src.write_text(
        "#@ ensures result[1] == p[1]\n"
        "def ident(p: tuple[int | None, int]) -> tuple[int | None, int]:\n"
        "    return p\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=80)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_filtered_comp_and_folds_translation_faithful(tmp_path):
    src = tmp_path / "folds.py"
    src.write_text(
        "#@ ensures len(result) <= len(xs)\n"
        "def positives(xs: list[int]) -> list[int]:\n"
        "    return [x for x in xs if x > 0]\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def sum_pos(xs: list[int]) -> int:\n"
        "    return sum(x for x in xs if x > 0)\n"
        "\n"
        "#@ ensures result == True or result == False\n"
        "def all_pos(xs: list[int]) -> bool:\n"
        "    return all(x > 0 for x in xs)\n"
        "\n"
        "#@ ensures result == True or result == False\n"
        "def any_zero(xs: list[int]) -> bool:\n"
        "    return any(x == 0 for x in xs)\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=80)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_foreach_tuple_unpack_translation_faithful(tmp_path):
    src = tmp_path / "pairs.py"
    src.write_text(
        "#@ ensures result == result\n"
        "def add_pairs(pairs: list[tuple[int, int]]) -> int:\n"
        "    s = 0\n"
        "    for a, b in pairs:\n"
        "        s = s + a + b\n"
        "    return s\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=80)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_walrus_translation_faithful(tmp_path):
    src = tmp_path / "walrus.py"
    src.write_text(
        "#@ ensures result == n\n"
        "def ident(n: int) -> int:\n"
        "    return (x := n)\n"
        "\n"
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def countdown(n: int) -> int:\n"
        "    x = n\n"
        "    s = 0\n"
        "    while (x := x - 1) >= 0:\n"
        "        #@ invariant s >= 0\n"
        "        #@ decreases x + 1\n"
        "        if x % 2 == 0:\n"
        "            continue\n"
        "        s = s + 1\n"
        "    return s\n"
        "\n"
        "#@ ensures result == n or result == 0\n"
        "def gated(n: int) -> int:\n"
        "    if (x := n) > 0:\n"
        "        return x\n"
        "    return 0\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=80)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]


def test_fstring_translation_faithful(tmp_path):
    src = tmp_path / "greet.py"
    src.write_text(
        "#@ ensures result == \"hi \" + s\n"
        "def greet(s: str) -> str:\n"
        "    return f\"hi {s}\"\n"
        "\n"
        "#@ ensures result == s\n"
        "def ident(s: str) -> str:\n"
        "    return f\"{s}\"\n"
        "\n"
        "#@ ensures result == a + b\n"
        "def glue(a: str, b: str) -> str:\n"
        "    return f\"{a}{b}\"\n"
    )
    result = difftest_file(src, tmp_path / "out", examples=80)
    assert result.error is None, result.error
    assert result.functions and all(f.ok for f in result.functions), [
        (f.name, f.mismatch, f.error) for f in result.functions
    ]
