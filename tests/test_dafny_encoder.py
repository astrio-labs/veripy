import pytest

from lemmapy.backends.dafny.encoder import EncodeError, encode_module
from lemmapy.frontend.extract import parse_source


def _encode(source: str) -> str:
    specs = parse_source(source)
    return encode_module(source, specs, module_name="m.py").dafny_source


BELOW = (
    "#@ ensures result == (forall i in range(len(l)) :: l[i] < t)\n"
    "def below_threshold(l: list[int], t: int) -> bool:\n"
    "    for i in range(len(l)):\n"
    "        #@ invariant forall k in range(i) :: l[k] < t\n"
    "        if l[i] >= t:\n"
    "            return False\n"
    "    return True\n"
)


def test_method_signature_and_types():
    dfy = _encode(BELOW)
    assert "method below_threshold(l: seq<int>, t: int) returns (result: bool)" in dfy


def test_forall_lowering_and_auto_bounds_invariant():
    dfy = _encode(BELOW)
    assert "forall i :: (0 <= i < |l|) ==> ((l[PyIndex(i, |l|)] < t))" in dfy
    assert "invariant i_lo <= i <= PyMax(i_lo, i_hi)" in dfy
    assert "invariant (forall k :: (0 <= k < i) ==> ((l[PyIndex(k, |l|)] < t)))" in dfy


def test_range_bounds_hoisted_once():
    # Python evaluates range() bounds once; the lowering must too.
    dfy = _encode(BELOW)
    assert "var i_lo, i_hi := 0, |l|;" in dfy
    assert "while i < i_hi" in dfy


def test_preamble_inlined():
    dfy = _encode(BELOW)
    assert "function PyMod(a: int, b: int): int" in dfy
    assert "// ---- STUB END" in dfy


def test_old_lowers_to_param():
    src = "#@ ensures result == old(x) + 1\ndef bump(x: int) -> int:\n    return x + 1\n"
    dfy = _encode(src)
    assert "ensures (result == (x + 1))" in dfy


def test_arithmetic_lowering():
    src = (
        "#@ requires b != 0\n"
        "#@ ensures result == a % b + a // b + min(a, b)\n"
        "def f(a: int, b: int) -> int:\n"
        "    return a % b + a // b + min(a, b)\n"
    )
    dfy = _encode(src)
    assert "PyMod(a, b)" in dfy
    assert "PyFloorDiv(a, b)" in dfy
    assert "PyMin(a, b)" in dfy


def test_iff_desugar_strips_bool():
    src = (
        "#@ ensures result <==> x > 0\n"
        "def f(x: int) -> bool:\n"
        "    return x > 0\n"
    )
    dfy = _encode(src)
    assert "ensures ((result) == ((x > 0)))" in dfy


def test_line_map_points_at_spec_lines():
    specs = parse_source(BELOW)
    encoded = encode_module(BELOW, specs, module_name="m.py")
    assert 1 in encoded.line_map.values()  # the ensures line


def _expect_encode_error(source: str, needle: str):
    specs = parse_source(source)
    with pytest.raises(EncodeError) as exc:
        encode_module(source, specs, module_name="m.py")
    assert needle in exc.value.message


def test_float_annotation_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0 or result < 0\ndef f(x: float) -> float:\n    return x\n",
        "outside the slice-1 encoder",
    )


def test_param_rebinding_rejected():
    _expect_encode_error(
        "#@ ensures result == x\ndef f(x: int) -> int:\n    x = x + 1\n    return x\n",
        "parameters are immutable",
    )


def test_negative_index_normalized_via_pyindex():
    src = (
        "#@ requires len(l) > 0\n#@ ensures result == l[-1]\n"
        "def f(l: list[int]) -> int:\n    return l[-1]\n"
    )
    dfy = _encode(src)
    assert "PyIndex((-1), |l|)" in dfy


def test_dynamic_index_wrapped_in_pyindex():
    # A variable index can be negative at runtime; Python normalizes, so the
    # lowering must too (a bare Dafny index would mis-report correct code).
    src = (
        "#@ requires -len(l) <= i < len(l)\n"
        "#@ ensures result == l[i]\n"
        "def f(l: list[int], i: int) -> int:\n    return l[i]\n"
    )
    dfy = _encode(src)
    assert "l[PyIndex(i, |l|)]" in dfy


def test_indexing_is_uniformly_wrapped():
    # Uniform wrapping (even for l[0]) keeps quantifier triggers matchable —
    # mixed bare/wrapped index terms break witness instantiation.
    src = (
        "#@ requires len(l) > 0\n#@ ensures result == l[0]\n"
        "def f(l: list[int]) -> int:\n    return l[0]\n"
    )
    dfy = _encode(src)
    assert "l[PyIndex(0, |l|)]" in dfy


def test_non_range_for_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\ndef f(l: list[int]) -> int:\n"
        "    s = 0\n    for v in l:\n        #@ invariant s >= 0\n        s = s + 1\n    return s\n",
        "range",
    )


def test_invariant_outside_loop_rejected():
    src = (
        "#@ ensures result == x\n"
        "def f(x: int) -> int:\n"
        "    #@ invariant x == x\n"
        "    return x\n"
    )
    _expect_encode_error(src, "top of a loop body")


# --- regressions from the adversarial encoder review (2026-08-12) ------------


def test_str_order_comparison_rejected():
    # Dafny seq `<` is prefix order; Python's is lexicographic.
    _expect_encode_error(
        '#@ ensures result == True or result == False\n'
        "def f(a: str, b: str) -> bool:\n    return a < b\n",
        "order comparison",
    )


def test_list_order_comparison_rejected():
    _expect_encode_error(
        "#@ ensures result == True or result == False\n"
        "def f(a: list[int], b: list[int]) -> bool:\n    return a <= b\n",
        "order comparison",
    )


def test_char_comparison_allowed():
    src = (
        "#@ requires len(s) >= 2\n"
        "#@ ensures result == (s[0] < s[1])\n"
        "def f(s: str) -> bool:\n    return s[0] < s[1]\n"
    )
    assert "s[PyIndex(0, |s|)] < s[PyIndex(1, |s|)]" in _encode(src)


def test_loop_index_read_after_loop_rejected():
    _expect_encode_error(
        "#@ requires n >= 1\n#@ ensures result == n\n"
        "def f(n: int) -> int:\n"
        "    for i in range(n):\n"
        "        pass\n"
        "    return i\n",
        "used after its loop",
    )


def test_mangle_is_injective_against_user_names():
    # `case` mangles; a user variable literally named case_py must not merge.
    src = (
        "#@ ensures result >= 1\n"
        "def f(c: bool) -> int:\n"
        "    case = 1\n"
        "    case_py = 2\n"
        "    return case + case_py\n"
    )
    dfy = _encode(src)
    assert "var case_py_ := 1;" in dfy
    assert "var case_py := 2;" in dfy


def test_hoisted_bound_temps_avoid_params():
    src = (
        "#@ requires i_lo >= 0\n"
        "#@ ensures result >= 0\n"
        "def f(i_lo: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(i_lo):\n"
        "        s = s + 1\n"
        "    return s\n"
    )
    dfy = _encode(src)
    assert "var i_lo_, i_hi := 0, i_lo;" in dfy


def test_bool_of_int_in_spec_rejected():
    _expect_encode_error(
        "#@ ensures result <==> x\n"
        "def f(x: int) -> bool:\n    return x != 0\n",
        "truthiness",
    )


def test_iff_on_bools_still_works():
    src = (
        "#@ ensures result <==> x > 0\n"
        "def f(x: int) -> bool:\n    return x > 0\n"
    )
    assert "==" in _encode(src)


def test_quantifier_binder_shadowing_rejected():
    _expect_encode_error(
        "#@ ensures result == (forall n in range(n) :: n >= 0)\n"
        "def f(n: int) -> bool:\n    return True\n",
        "shadows",
    )


def test_for_target_shadowing_param_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(x: int, n: int) -> int:\n"
        "    for x in range(n):\n"
        "        pass\n"
        "    return 0\n",
        "shadow",
    )


def test_duplicate_def_rejected():
    _expect_encode_error(
        "#@ ensures result == 1\n"
        "def f(x: int) -> int:\n    return 1\n"
        "def f(x: int) -> int:\n    return 2\n",
        "duplicate definition",
    )


def test_branch_assigned_local_is_hoisted():
    src = (
        "#@ ensures result >= 1\n"
        "def f(c: bool) -> int:\n"
        "    if c:\n"
        "        x = 1\n"
        "    else:\n"
        "        x = 2\n"
        "    return x\n"
    )
    dfy = _encode(src)
    assert "var x: int;" in dfy
    assert "x := 1;" in dfy and "x := 2;" in dfy


def test_list_augassign_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= len(a)\n"
        "def f(a: list[int], b: list[int]) -> list[int]:\n"
        "    x = a\n"
        "    x += b\n"
        "    return x\n",
        "augmented assignment",
    )


def test_carriage_return_in_literal_rejected():
    _expect_encode_error(
        '#@ ensures result == "a\\rb"\n'
        'def f() -> str:\n    return "a\\rb"\n',
        "control character",
    )


def test_in_against_string_rejected():
    # Python `in` on str is substring search; Dafny's is element membership.
    _expect_encode_error(
        "#@ ensures result == True or result == False\n"
        "def f(a: str, b: str) -> bool:\n    return a in b\n",
        "substring",
    )


def test_sequential_loops_reuse_index():
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        s = s + 1\n"
        "    for i in range(n):\n"
        "        s = s + 1\n"
        "    return s\n"
    )
    dfy = _encode(src)
    assert dfy.count("var i :=") == 1  # second loop reuses, no duplicate local
