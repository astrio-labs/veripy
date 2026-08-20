import pytest

from veripy.backends.dafny.encoder import EncodeError, encode_module
from veripy.backends.dafny.preamble import PREAMBLE_NAMES
from veripy.frontend.extract import parse_source


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
    # 0-based binders index BARE (trigger-compatible with body terms).
    dfy = _encode(BELOW)
    assert "forall i :: (0 <= i < |l|) ==> ((l[i] < t))" in dfy
    assert "invariant i_lo <= i <= PyMax(i_lo, i_hi)" in dfy
    assert "invariant (forall k :: (0 <= k < i) ==> ((l[k] < t)))" in dfy


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


def test_keyword_only_params_encode_as_ordinary_params():
    src = (
        "#@ requires lo <= hi\n"
        "#@ ensures lo <= result <= hi\n"
        "def clamp_kw(x: int, *, lo: int, hi: int) -> int:\n"
        "    return min(max(x, lo), hi)\n"
    )
    dfy = _encode(src)
    assert "method clamp_kw(x: int, lo: int, hi: int) returns (result: int)" in dfy


def test_actual_defaults_still_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(x: int, *, k: int = 3) -> int:\n    return x + k\n",
        "defaults",
    )


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


def test_index_policy_bare_when_provably_nonneg():
    # Policy: provably nonneg indices (literals, 0-based binders and loop
    # vars) index bare — keeping spec and body terms trigger-compatible —
    # everything else goes through PyIndex.
    src = (
        "#@ requires len(l) > 0\n#@ ensures result == l[0]\n"
        "def f(l: list[int]) -> int:\n    return l[0]\n"
    )
    assert "l[0]" in _encode(src)

    loop_src = (
        "#@ requires n >= 0 and n <= len(l)\n"
        "#@ ensures result >= 0 or result < 0\n"
        "def g(l: list[int], n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        s = s + l[i]\n"
        "    return s\n"
    )
    dfy = _encode(loop_src)
    assert "l[i]" in dfy
    assert "l[PyIndex" not in dfy


def test_for_each_over_non_list_rejected():
    # for-each over lists is supported (slice 3); other iterables are not.
    _expect_encode_error(
        "#@ ensures result >= 0\ndef f(n: int) -> int:\n"
        "    s = 0\n    for v in n:\n        s = s + 1\n    return s\n",
        "list-typed",
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
    assert "s[0] < s[1]" in _encode(src)


# --- slice 4: Optionals, slices, seq-max, assert ------------------------------


def test_optional_type_maps_to_pyopt():
    src = (
        "#@ ensures result >= 0 or result < 0\n"
        "def f(x: int | None) -> int:\n"
        "    if x is None:\n"
        "        return 0\n"
        "    return x\n"
    )
    dfy = _encode(src)
    assert "method f(x: PyOpt<int>) returns (result: int)" in dfy
    assert "if ((x).PyNone?)" in dfy
    assert "result := (x).v;" in dfy  # narrowing replayed as a .v VC


def test_none_assignment_and_some_injection():
    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    m: int | None = None\n"
        "    m = n\n"
        "    if m is not None:\n"
        "        return m\n"
        "    return 0\n"
    )
    dfy = _encode(src)
    assert "var m: PyOpt<int> := PyNone;" in dfy
    assert "m := PySome(n);" in dfy
    assert "(m).PySome?" in dfy


def test_optional_equality_never_raises():
    # Python `==` with a None-holding Optional is False, not an error:
    # the lowering must not emit a bare .v projection.
    src = (
        "#@ ensures result == (x == y)\n"
        "def f(x: int | None, y: int) -> bool:\n"
        "    return x == y\n"
    )
    dfy = _encode(src)
    assert "(x).PySome? && (x).v == y" in dfy


def test_tuple_assignment_coerces_optionals():
    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    x: int | None = None\n"
        "    y: int | None = None\n"
        "    x, y = n, None\n"
        "    if x is not None:\n"
        "        return x\n"
        "    return 0\n"
    )
    dfy = _encode(src)
    assert "x, y := PySome(n), PyNone;" in dfy


def test_optional_truthiness_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(x: int | None) -> int:\n"
        "    if x:\n"
        "        return 1\n"
        "    return 0\n",
        "is None",
    )


def test_is_on_non_optional_rejected():
    _expect_encode_error(
        "#@ ensures result == True or result == False\n"
        "def f(a: list[int], b: list[int]) -> bool:\n    return a is b\n",
        "is [not] None",
    )


def test_slice_lowers_to_pyslice():
    src = (
        "#@ ensures len(result) <= len(l)\n"
        "def f(l: list[int]) -> list[int]:\n"
        "    return l[1:-1]\n"
    )
    dfy = _encode(src)
    assert "PySlice(l, 1, (-1))" in dfy


def test_open_slice_bounds():
    src = (
        "#@ ensures len(result) <= len(l)\n"
        "def f(l: list[int]) -> list[int]:\n"
        "    return l[:2]\n"
    )
    assert "PySlice(l, 0, 2)" in _encode(src)


def test_one_arg_max_lowers_to_pyseqmax():
    src = (
        "#@ requires len(l) > 0\n"
        "#@ ensures result == max(l)\n"
        "def f(l: list[int]) -> int:\n    return max(l)\n"
    )
    assert "PySeqMax(l)" in _encode(src)


def test_assert_lowers_to_dafny_assert():
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result == n\n"
        "def f(n: int) -> int:\n"
        "    assert n >= 0\n"
        "    return n\n"
    )
    assert "assert (n >= 0);" in _encode(src)


def test_assert_nonliteral_message_rejected():
    _expect_encode_error(
        "#@ requires n >= 0\n"
        "#@ ensures result == n\n"
        "def f(n: int) -> int:\n"
        "    assert n >= 0, str(n)\n"
        "    return n\n",
        "assert messages must be literals",
    )


# --- sum() folds (slice 6) ------------------------------------------------------


def test_sum_encodes_to_pysum_in_spec_and_code():
    src = (
        "#@ ensures result == sum(l)\n"
        "def f(l: list[int]) -> int:\n"
        "    total = sum(l)\n"
        "    return total\n"
    )
    assert _encode(src).count("PySum(l)") == 2


def test_sum_over_slice():
    src = (
        "#@ ensures result == sum(l[:2])\n"
        "def f(l: list[int]) -> int:\n"
        "    return sum(l[:2])\n"
    )
    assert "PySum(PySlice(l, 0, 2))" in _encode(src)


def test_sum_of_genexp_maps_then_folds():
    src = (
        "#@ ensures result == sum(x * x for x in l)\n"
        "def f(l: list[int]) -> int:\n"
        "    return sum(x * x for x in l)\n"
    )
    out = _encode(src)
    assert out.count("PySum(seq(|l|") == 2


def test_sum_needs_int_list():
    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    return sum(n)\n"
    )
    with pytest.raises(EncodeError, match="list\\[int\\]"):
        _encode(src)


def test_sum_of_filtered_genexp_skips_with_zero():
    src = (
        "#@ ensures result >= 0\n"
        "def f(l: list[int]) -> int:\n"
        "    return sum(x for x in l if x > 0)\n"
    )
    dfy = _encode(src)
    assert "else 0)" in dfy
    assert "PySum(seq(|l|" in dfy


def test_sum_of_non_int_genexp_rejected():
    src = (
        "#@ ensures result >= 0\n"
        "def f(l: list[int]) -> int:\n"
        "    return sum(l[:x] for x in l)\n"
    )
    with pytest.raises(EncodeError, match="int-valued"):
        _encode(src)


def test_two_arg_sum_rejected():
    src = (
        "#@ ensures result >= 0\n"
        "def f(l: list[int]) -> int:\n"
        "    return sum(l, 1)\n"
    )
    with pytest.raises(EncodeError, match="outside the slice"):
        _encode(src)


def test_keyword_arguments_rejected_not_dropped():
    # Silently dropping a keyword (max's key=...) would change the meaning.
    src = (
        "#@ ensures result == a or result == b\n"
        "def f(a: int, b: int) -> int:\n"
        "    return max(a, b, key=abs)\n"
    )
    with pytest.raises(EncodeError, match="keyword arguments"):
        _encode(src)


# --- pow (slice 7) --------------------------------------------------------------


def test_pow_encodes_to_pypow_in_spec_and_code():
    src = (
        "#@ requires e >= 0\n"
        "#@ ensures result == b ** e\n"
        "def f(b: int, e: int) -> int:\n"
        "    return b ** e\n"
    )
    assert _encode(src).count("PyPow(b, e)") == 2


def test_pow_on_non_int_rejected():
    src = (
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return xs ** 2\n"
    )
    with pytest.raises(EncodeError, match="Python has no `\\*\\*`"):
        _encode(src)


# --- builtin shadowing / binder capture (adversarial round on slice 6) ----------


def test_module_level_def_shadowing_builtin_rejected():
    # An unspecced `def sum` vanishes from the Dafny model while call sites
    # encode as the builtin: verified-but-false unless rejected.
    src = (
        "def sum(xs: list[int]) -> int:\n"
        "    return 1\n"
        "\n"
        "\n"
        "#@ ensures result == 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return sum(xs[:0])\n"
    )
    with pytest.raises(EncodeError, match="shadows a builtin"):
        _encode(src)


def test_module_level_assignment_and_import_shadowing_rejected():
    for line in ("sum = 5\n", "from math import prod as sum\n"):
        src = line + "#@ ensures result == 0\ndef f() -> int:\n    return 0\n"
        with pytest.raises(EncodeError, match="shadows a builtin"):
            _encode(src)


def test_parameter_shadowing_builtin_rejected():
    # CPython raises TypeError calling an int; Dafny would model builtin sum.
    src = (
        "#@ ensures result == 0\n"
        "def h(sum: int) -> int:\n"
        "    return sum\n"
    )
    with pytest.raises(EncodeError, match="shadows a builtin"):
        _encode(src)


def test_local_shadowing_builtin_rejected():
    src = (
        "#@ ensures result == 3\n"
        "def g(x: int) -> int:\n"
        "    abs = 0\n"
        "    return abs\n"
    )
    with pytest.raises(EncodeError, match="shadows a builtin"):
        _encode(src)


def test_module_level_match_capture_shadowing_rejected():
    # Pattern captures bind via name attributes, not ast.Name(Store) —
    # `case sum:` rebinds the builtin just like `sum = ...` does.
    for pattern in ("case sum:", "case [*sum]:", "case {**sum}:"):
        src = (
            "x = [1]\n"
            "match x:\n"
            f"    {pattern}\n"
            "        pass\n"
            "\n"
            "#@ ensures result == 0\n"
            "def f(xs: list[int]) -> int:\n"
            "    return 0\n"
        )
        with pytest.raises(EncodeError, match="shadows a builtin"):
            _encode(src)


def test_quantifier_binder_capture_by_genexp_binder_rejected():
    # A quantifier binder colliding with an enclosing comprehension binder
    # would be rewritten by name_overrides — the quantified variable would
    # go unused and the spec would mean something else than CPython.
    src = (
        "#@ ensures result == sum((1 if all(x >= 0 for x in xs) else 0) for x in xs)\n"
        "def f(xs: list[int]) -> int:\n"
        "    return 0\n"
    )
    with pytest.raises(EncodeError, match="shadows an existing name"):
        _encode(src)


def test_preamble_names_are_exactly_the_globally_visible_declarations():
    # The reserved set is scraped out of the preamble TEXT so a declaration
    # added later is reserved without anyone remembering to. The cost is
    # that a preamble rewritten in a shape the scraper cannot parse would
    # leave the set empty and reopen the hole with every test still green,
    # so v0.7's globally visible names are pinned here: growing the
    # preamble has to be a deliberate edit in this test too.
    assert PREAMBLE_NAMES == {
        "PyMod", "PyFloorDiv", "PyMin", "PyMax", "PyAbs", "PyIndex",
        "PySlice", "PySeqMax", "PySeqMin", "PySum", "PyFlatten", "PyPow",
        "PyGcd", "PyFact", "PyIsqrt",
        "PyDigit", "PyNatToStr", "PyIntToStr", "PyIsDigits", "PyIsIntStr",
        "PyDigitsToNat", "PyStrToInt",
        "PyInsert", "PySorted",
        "PyOpt", "PyNone", "PySome",
        "PyExn", "ValueError", "IndexError", "ZeroDivisionError",
        "TypeError", "KeyError",
        "PyOutcome", "PyOk", "PyErr",
        "PyStrFind", "PyStrJoin", "PyStrSplit", "PyStrStartsWith",
        "PyStrEndsWith", "PyStrReplace", "PyStrLStrip", "PyStrRStrip",
        "PyStrStrip",
    }
    # Datatype members are reached only through a receiver, so they are not
    # in the top-level scope and a Python name equal to one cannot collide.
    assert not ({"IsFailure", "PropagateFailure", "Extract"} & PREAMBLE_NAMES)


def test_module_name_colliding_with_preamble_declaration_rejected():
    # The preamble is inlined into the same Dafny scope as the encoded
    # module, so `def PyExn` emitted a second top-level PyExn and Dafny
    # answered "duplicate name of top-level declaration" against generated
    # code — a resolver error on a file the user never wrote.
    for name in sorted(PREAMBLE_NAMES):
        src = (
            "#@ ensures result == x\n"
            f"def {name}(x: int) -> int:\n"
            "    return x\n"
        )
        with pytest.raises(EncodeError, match="collides with a declaration"):
            _encode(src)
    # Module-level bindings that are not defs land in the same scope.
    for line in ("PySum = 5\n", "from math import prod as PyMax\n"):
        src = line + "#@ ensures result == 0\ndef f() -> int:\n    return 0\n"
        with pytest.raises(EncodeError, match="collides with a declaration"):
            _encode(src)


def test_local_param_and_binder_colliding_with_preamble_rejected():
    # `sum(...)` in a spec encodes to a CALL of the preamble's PySum; a
    # local, parameter or binder of that name shadows the function at the
    # call site and Dafny reports "non-function expression is called with
    # parameters" — again against generated Dafny, not the Python line.
    cases = (
        "#@ ensures result == sum(xs)\n"
        "def f(xs: list[int]) -> int:\n"
        "    PySum = 0\n"
        "    return PySum\n",

        "#@ ensures result == 0\n"
        "def g(PyMod: int) -> int:\n"
        "    return 0\n",

        "#@ ensures forall PySum in range(len(xs)) :: sum(xs[:PySum]) >= 0\n"
        "def h(xs: list[int]) -> int:\n"
        "    return 0\n",

        "#@ ensures result == sum(PyAbs for PyAbs in xs)\n"
        "def k(xs: list[int]) -> int:\n"
        "    return 0\n",
    )
    for src in cases:
        with pytest.raises(EncodeError, match="collides with a declaration"):
            _encode(src)


def test_range_keywords_rejected_everywhere():
    # range() takes no keywords in CPython (TypeError); the structural
    # matchers must not read `range(5, step=2)` as `range(5)`. The spec
    # position is the dangerous one — specs are comments, invisible to
    # the type gate.
    spec_side = (
        "#@ ensures result == 0 or (forall i in range(5, step=2) :: i >= 0)\n"
        "def f() -> int:\n"
        "    return 0\n"
    )
    comp_side = (
        "#@ ensures len(result) >= 0\n"
        "def g() -> list[int]:\n"
        "    return [i for i in range(5, step=2)]\n"
    )
    loop_side = (
        "#@ ensures result >= 0\n"
        "def h() -> int:\n"
        "    t = 0\n"
        "    for i in range(5, step=2):\n"
        "        t = t + 1\n"
        "    return t\n"
    )
    for src in (spec_side, comp_side, loop_side):
        with pytest.raises(EncodeError):
            _encode(src)


def test_sum_of_optional_genexp_projects_through_deopt():
    # sum over list[int | None]: elements project through .v, whose
    # well-formedness VC is exactly Python's would-raise-TypeError condition.
    src = (
        "#@ ensures result >= 0 or result < 0\n"
        "def f(l: list[int | None]) -> int:\n"
        "    return sum(x for x in l)\n"
    )
    assert ").v" in _encode(src)


def test_int_truthiness_condition_rejected_at_encode_time():
    src = (
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    if sum(xs):\n"
        "        return 1\n"
        "    return 0\n"
    )
    with pytest.raises(EncodeError, match="truthiness"):
        _encode(src)


# --- proof additions (#@ proof + sidecar) --------------------------------------


def _encode_with_lemmas(source: str, lemmas: set[str]) -> str:
    specs = parse_source(source)
    return encode_module(
        source, specs, module_name="m.py", proof_lemmas=frozenset(lemmas)
    ).dafny_source


PROOF_IN_WHILE = (
    "#@ requires n >= 0\n"
    "#@ ensures result >= 0\n"
    "def f(n: int) -> int:\n"
    "    s = 0\n"
    "    while s < n:\n"
    "        #@ invariant 0 <= s <= max(n, 0)\n"
    "        #@ proof HelperLemma(s, max(n, 0))\n"
    "        s = s + 1\n"
    "    return s\n"
)


def test_proof_clause_emits_ghost_lemma_call():
    dfy = _encode_with_lemmas(PROOF_IN_WHILE, {"HelperLemma"})
    assert "HelperLemma(s, PyMax(n, 0));" in dfy
    # emitted INSIDE the loop body, before the statement that follows it
    body = dfy[dfy.index("while (s < n)"):]
    assert body.index("HelperLemma") < body.index("s := (s + 1);")


def test_proof_clause_target_must_be_declared_lemma():
    specs = parse_source(PROOF_IN_WHILE)
    with pytest.raises(EncodeError) as exc:
        encode_module(PROOF_IN_WHILE, specs, module_name="m.py")
    assert "unknown lemma" in exc.value.message


def test_proof_clause_works_inside_foreach_body():
    src = (
        "#@ ensures result >= 0 or result < 0\n"
        "def f(l: list[int]) -> int:\n"
        "    s = 0\n"
        "    for v in l:\n"
        "        #@ proof StepFact(s)\n"
        "        s = s + v\n"
        "    return s\n"
    )
    dfy = _encode_with_lemmas(src, {"StepFact"})
    inner = dfy[dfy.index("var v :="):]
    assert inner.index("StepFact(s);") < inner.index("s := (s + v);")


def test_trailing_proof_clause_rejected():
    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    if n > 0:\n"
        "        s = 1\n"
        "        #@ proof StepFact(s)\n"
        "    return 0\n"
    )
    specs = parse_source(src)
    with pytest.raises(EncodeError) as exc:
        encode_module(src, specs, module_name="m.py", proof_lemmas=frozenset({"StepFact"}))
    assert "trails its block" in exc.value.message


def test_proof_clause_must_be_a_call():
    src = (
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    #@ proof n + 1\n"
        "    return 0\n"
    )
    specs = parse_source(src)
    (fn,) = specs.functions
    assert fn.errors and "lemma call" in fn.errors[0].error


def _sidecar_error(tmp_path, content: str) -> str:
    from veripy.backends.dafny.encoder import load_proof_sidecar

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (tmp_path / "m.proofs.dfy").write_text(content)
    with pytest.raises(EncodeError) as exc:
        load_proof_sidecar(src)
    return exc.value.message


def test_proof_sidecar_rejects_methods(tmp_path):
    assert "not allowed" in _sidecar_error(tmp_path, "method Evil() { print 1; }\n")


def test_proof_sidecar_rejects_comment_prefixed_method(tmp_path):
    # A blacklist keyed on line starts would miss this.
    assert "not allowed" in _sidecar_error(
        tmp_path, "/* innocent */ method Evil() {}\n"
    )


def test_proof_sidecar_rejects_axioms(tmp_path):
    # A bodiless lemma is an axiom — anything would verify.
    assert "axiom" in _sidecar_error(
        tmp_path, "lemma FreeLunch(x: int)\n  ensures x == x + 1\n"
    )


def test_proof_sidecar_rejects_setliteral_axiom_masquerade(tmp_path):
    # A bodiless lemma whose ensures ends in a set literal must not have the
    # literal's brace counted as its body (that would admit an axiom).
    msg = _sidecar_error(
        tmp_path, "lemma FreeLunch(x: int)\n  ensures x in {1, 2}\n"
    )
    assert "masquerade" in msg or "axiom" in msg


def test_proof_sidecar_rejects_multiset_display_masquerade(tmp_path):
    # `multiset{1}`'s brace follows an identifier — must not count as a body.
    msg = _sidecar_error(
        tmp_path, "lemma FreeLunch(x: int)\n  ensures x in multiset{1}\n"
    )
    assert "not allowed" in msg


def test_proof_sidecar_rejects_lambda_arrows(tmp_path):
    # A lambda's body brace follows `>`; forbid isolated `=>` outright.
    msg = _sidecar_error(
        tmp_path, "lemma FreeLunch(x: int)\n  ensures (y => true)(x)\n"
    )
    assert "lambda" in msg


def test_proof_sidecar_bodiless_lemma_not_rescued_by_successor(tmp_path):
    # A later declaration's body must not retroactively "prove" an earlier
    # bodiless lemma.
    msg = _sidecar_error(
        tmp_path,
        "lemma FreeLunch(x: int)\n  ensures x == x + 1\n"
        "lemma Honest(x: int)\n  ensures x == x\n{\n}\n",
    )
    assert "axiom" in msg


def test_proof_clause_leading_else_branch_accepted():
    src = (
        "#@ ensures result >= 0\n"
        "def f(c: bool, n: int) -> int:\n"
        "    if c:\n"
        "        s = 1\n"
        "    else:\n"
        "        #@ proof StepFact(n)\n"
        "        s = 2\n"
        "    return s\n"
    )
    dfy = _encode_with_lemmas(src, {"StepFact"})
    else_part = dfy[dfy.index("} else {"):]
    assert "StepFact(n);" in else_part
    assert else_part.index("StepFact(n);") < else_part.index("s := 2;")


def test_proof_sidecar_string_brace_cannot_be_a_body(tmp_path):
    # A `{` inside a string literal must never count as declaration
    # structure — string interiors are blanked before tokenization.
    msg = _sidecar_error(
        tmp_path,
        'lemma FreeLunch(s: string)\n  ensures s != "a{"\n',
    )
    assert "axiom" in msg


def test_proof_sidecar_verbatim_strings_forbidden(tmp_path):
    msg = _sidecar_error(
        tmp_path,
        'lemma L(s: string)\n  ensures s != @"x"\n{\n}\n',
    )
    assert "@" in msg


def test_proof_sidecar_string_in_body_still_fine(tmp_path):
    from veripy.backends.dafny.encoder import load_proof_sidecar

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (tmp_path / "m.proofs.dfy").write_text(
        'lemma L(s: string)\n  ensures s == s\n{\n  assert "{{" == "{{";\n}\n'
    )
    assert "L" in load_proof_sidecar(src).lemmas


def test_proof_sidecar_implication_still_legal(tmp_path):
    from veripy.backends.dafny.encoder import load_proof_sidecar

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (tmp_path / "m.proofs.dfy").write_text(
        "lemma Imp(x: int)\n  ensures x > 1 ==> x > 0\n{\n}\n"
    )
    assert "Imp" in load_proof_sidecar(src).lemmas


def test_proof_sidecar_body_after_signature_still_accepted(tmp_path):
    from veripy.backends.dafny.encoder import load_proof_sidecar

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (tmp_path / "m.proofs.dfy").write_text(
        "lemma L(x: int)\n  ensures x == x\n{\n  assert x == x;\n}\n"
    )
    assert "L" in load_proof_sidecar(src).lemmas


def test_proof_sidecar_rejects_assume_and_attributes(tmp_path):
    assert "not allowed" in _sidecar_error(
        tmp_path, "lemma L(x: int) ensures x == x { assume x == x; }\n"
    )
    assert "attributes" in _sidecar_error(
        tmp_path, "lemma {:axiom} L(x: int) ensures x == x\n"
    )


def test_proof_sidecar_loads_lemmas(tmp_path):
    from veripy.backends.dafny.encoder import load_proof_sidecar

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (tmp_path / "m.proofs.dfy").write_text(
        "lemma Triv(x: int)\n  ensures x == x\n{\n}\n"
    )
    sidecar = load_proof_sidecar(src)
    assert "lemma Triv" in sidecar.text
    assert "Triv" in sidecar.lemmas


def _sidecar_rule(content: str) -> str | None:
    from veripy.backends.dafny.encoder import validate_sidecar_text

    with pytest.raises(EncodeError) as exc:
        validate_sidecar_text(content, "m.proofs.dfy")
    return exc.value.rule


def test_sidecar_rejection_rules_classified():
    # Telemetry: every whitelist rejection carries a machine-readable rule
    # id, so the repair loop can report WHICH rule an engine proposal
    # tripped (the paper's "attempted axioms" number).
    assert _sidecar_rule(
        "lemma FreeLunch(x: int)\n  ensures x == x + 1\n") == "bodiless"
    assert _sidecar_rule(
        "lemma L(x: int) ensures x == x { assume x == x; }\n"
    ) == "forbidden-token"
    assert _sidecar_rule(
        "lemma {:axiom} L(x: int) ensures x == x\n") == "attribute"
    assert _sidecar_rule(
        "lemma L(x: int)\n  ensures (y => true)(x)\n{\n}\n") == "lambda"
    assert _sidecar_rule(
        "lemma L(x: int)\n  ensures x in {1, 2}\n{\n}\n") == "spec-literal"
    assert _sidecar_rule("assert 1 == 1;\n") == "non-declaration"
    assert _sidecar_rule(
        "ghost lemma L(x: int)\n  ensures x == x\n{\n}\n") == "malformed-ghost"
    assert _sidecar_rule(
        "lemma L(x: int)\n  ensures x in multiset{1}\n{\n}\n"
    ) == "forbidden-token"


def test_validate_sidecar_text_accepts_good_pack():
    from veripy.backends.dafny.encoder import validate_sidecar_text

    lemmas = validate_sidecar_text(
        "lemma A(x: int)\n  ensures x == x\n{\n}\n"
        "lemma B(x: int)\n  ensures x <= x\n{\n  A(x);\n}\n",
        "m.proofs.dfy",
    )
    assert lemmas == frozenset({"A", "B"})


def test_sidecar_decreases_cardinality_before_body_accepted():
    # `decreases |s|` right before the body brace is idiomatic Dafny; the
    # closing pipe must count as a value ender or every engine writing it
    # burns an iteration on a false rejection.
    from veripy.backends.dafny.encoder import validate_sidecar_text

    lemmas = validate_sidecar_text(
        "lemma Sum(s: seq<int>)\n  ensures 0 <= |s|\n  decreases |s|\n"
        "{\n  if |s| > 0 { Sum(s[..|s|-1]); }\n}\n",
        "m.proofs.dfy",
    )
    assert lemmas == frozenset({"Sum"})


def test_sidecar_cardinality_of_display_still_no_masquerade():
    # `ensures 0 <= |{x}|`: the display brace follows `|` and would now
    # count as a body — but the cardinality's CLOSING pipe then dangles at
    # top level, tripping the declaration scan. No bodiless lemma slips
    # through via cardinality-of-display.
    assert _sidecar_rule(
        "lemma FreeLunch(x: int)\n  ensures 0 <= |{x}|\n"
    ) == "non-declaration"
    # And the plain display in spec position stays blocked as before.
    assert _sidecar_rule(
        "lemma FreeLunch(x: int)\n  ensures x in {1, 2}\n"
    ) == "spec-literal"


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


# --- slice 3: list building ---------------------------------------------------


APPEND_OK = (
    "#@ requires n >= 0\n"
    "#@ ensures len(result) == n\n"
    "def zeros(n: int) -> list[int]:\n"
    "    out: list[int] = []\n"
    "    for i in range(n):\n"
    "        #@ invariant len(out) == i\n"
    "        out.append(0)\n"
    "    return out\n"
)


def test_append_lowers_to_seq_concat():
    dfy = _encode(APPEND_OK)
    assert "out := out + [0];" in dfy


def test_append_on_parameter_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(l: list[int]) -> list[int]:\n"
        "    l.append(1)\n"
        "    return l\n",
        "ownership",
    )


def test_append_after_aliasing_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f() -> list[int]:\n"
        "    xs: list[int] = []\n"
        "    ys = xs\n"
        "    xs.append(1)\n"
        "    return ys\n",
        "ownership",
    )


def test_append_while_iterating_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f() -> list[int]:\n"
        "    xs: list[int] = [1]\n"
        "    for v in xs:\n"
        "        xs.append(v)\n"
        "    return xs\n",
        "iterating",
    )


def test_empty_list_needs_annotation():
    _expect_encode_error(
        "#@ ensures len(result) == 0\n"
        "def f() -> list[int]:\n"
        "    out = []\n"
        "    return out\n",
        "annotate the empty list",
    )


def test_list_comprehension_lowers_to_seq_constructor():
    src = (
        "#@ ensures len(result) == len(l)\n"
        "def f(l: list[int]) -> list[int]:\n"
        "    return [(e + 1) for e in l]\n"
    )
    dfy = _encode(src)
    assert "seq(|l|, e_c requires 0 <= e_c < |l| => (l[e_c] + 1))" in dfy


def test_filtered_comprehension_flattens_kept_elements():
    src = (
        "#@ ensures len(result) <= len(l)\n"
        "def f(l: list[int]) -> list[int]:\n"
        "    return [e for e in l if e > 0]\n"
    )
    dfy = _encode(src)
    assert "PyFlatten(seq(|l|" in dfy
    assert "then [l[e_c]] else []" in dfy


def test_list_truthiness_in_conditions():
    src = (
        "#@ ensures result == (len(l) == 0)\n"
        "def f(l: list[int]) -> bool:\n"
        "    if not l:\n"
        "        return True\n"
        "    return False\n"
    )
    dfy = _encode(src)
    assert "if (|l| == 0)" in dfy


def test_foreach_lowering_snapshots_iterable():
    src = (
        "#@ ensures result >= 0 or result < 0\n"
        "def f(l: list[int]) -> int:\n"
        "    s = 0\n"
        "    for v in l:\n"
        "        s = s + v\n"
        "    return s\n"
    )
    dfy = _encode(src)
    assert "var v_it := l;" in dfy
    assert "var v := v_it[v_i];" in dfy


def test_foreach_unpacks_list_of_tuples():
    src = (
        "#@ ensures result >= 0 or result < 0\n"
        "def f(pairs: list[tuple[int, int]]) -> int:\n"
        "    s = 0\n"
        "    for a, b in pairs:\n"
        "        s = s + a + b\n"
        "    return s\n"
    )
    dfy = _encode(src)
    assert "var a, b := a_it[a_i].0, a_it[a_i].1;" in dfy


def test_foreach_unpack_arity_mismatch_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(pairs: list[tuple[int, int, int]]) -> int:\n"
        "    s = 0\n"
        "    for a, b in pairs:\n"
        "        s = s + a + b\n"
        "    return s\n",
        "arity 3",
    )


def test_foreach_unpack_needs_list_of_tuples():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    s = 0\n"
        "    for a, b in xs:\n"
        "        s = s + a\n"
        "    return s\n",
        "list of tuples",
    )


def test_foreach_target_read_after_loop_rejected():
    _expect_encode_error(
        "#@ requires len(l) > 0\n#@ ensures result == result\n"
        "def f(l: list[int]) -> int:\n"
        "    for v in l:\n"
        "        pass\n"
        "    return v\n",
        "used after its loop",
    )


def test_foreach_invariant_referencing_target_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0 or result < 0\n"
        "def f(l: list[int]) -> int:\n"
        "    s = 0\n"
        "    for v in l:\n"
        "        #@ invariant v >= 0 or v < 0\n"
        "        s = s + v\n"
        "    return s\n",
        "not in scope at the loop head",
    )


def test_expression_selected_iterable_still_freezes():
    # `for v in (xs if flag else [2])` iterates xs on one path — appending
    # to xs mid-loop must be rejected even though the iterable is not a
    # bare name (CPython's live iterator vs the lowering's snapshot).
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(flag: bool) -> list[int]:\n"
        "    xs: list[int] = [1]\n"
        "    for v in (xs if flag else [2]):\n"
        "        xs.append(v)\n"
        "    return xs\n",
        "iterating",
    )


def test_nested_foreach_same_list_keeps_freeze():
    # The inner loop over the same list must not thaw the outer iteration.
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f() -> list[int]:\n"
        "    xs: list[int] = [1, 2]\n"
        "    for v in xs:\n"
        "        for w in xs:\n"
        "            pass\n"
        "        xs.append(v)\n"
        "    return xs\n",
        "iterating",
    )


def test_ownership_merges_across_branches():
    # `xs` aliases on one path: not owned after the join, whatever the
    # branch order.
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(c: bool) -> list[int]:\n"
        "    ys: list[int] = []\n"
        "    xs: list[int] = []\n"
        "    if c:\n"
        "        xs = ys\n"
        "    else:\n"
        "        xs = [1]\n"
        "    xs.append(0)\n"
        "    return xs\n",
        "ownership",
    )


def test_ownership_lost_in_then_branch_without_else():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(c: bool) -> list[int]:\n"
        "    xs: list[int] = []\n"
        "    if c:\n"
        "        ys = xs\n"
        "    xs.append(1)\n"
        "    return xs\n",
        "ownership",
    )


def test_ownership_survives_branches_without_aliasing():
    src = (
        "#@ ensures len(result) >= 1\n"
        "def f(c: bool) -> list[int]:\n"
        "    xs: list[int] = []\n"
        "    if c:\n"
        "        xs.append(1)\n"
        "    else:\n"
        "        xs.append(2)\n"
        "    xs.append(3)\n"
        "    return xs\n"
    )
    dfy = _encode(src)
    assert dfy.count("xs := xs + [") == 3


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


# --- binary-operator operand types: `check` must reject what Dafny would ------
#
# These all passed `check` as "conformant" and then failed INSIDE Dafny with
# a message about `seq<char>`, breaking the M1 rule that the encoder dry-run
# is the conformance authority.

def _reject(src: str, pattern: str):
    with pytest.raises(EncodeError, match=pattern):
        _encode(src)


def _fn(body: str, sig: str = "a: str, b: str", ret: str = "str") -> str:
    return (f"#@ ensures len(result) >= 0\n"
            f"def f({sig}) -> {ret}:\n"
            f"    return {body}\n")


def test_str_repetition_is_named_as_python_legal_but_unmodelled():
    # Python DOES define `s * n`; the message must not imply the program is
    # wrong, only that the fragment has not grown to it.
    _reject(_fn("a * 2", "a: str"), "sequence repetition")
    _reject(_fn("2 * a", "a: str"), "sequence repetition")  # mirrored operands
    _reject(_fn("xs * 2", "xs: list[int]", "list[int]"), "sequence repetition")


def test_string_formatting_percent_is_not_integer_modulo():
    # `s % x` silently encoded to PyMod(seq<char>, int).
    _reject(_fn("a % b", "a: str, b: int"), "printf-style string formatting")


def test_bool_arithmetic_names_the_coercion_it_relies_on():
    # `True + True == 2` in Python; Dafny has no such coercion, so this
    # could never have worked -- but it was accepted by `check`.
    _reject("#@ ensures result >= 0\ndef f(a: bool, b: bool) -> int:\n    return a + b\n",
            "bool-to-int coercion")


@pytest.mark.parametrize("body,sig,ret", [
    ("a - b", "a: str, b: str", "str"),
    ("a + b", "a: str, b: int", "str"),
    ("a + b", "a: int, b: str", "int"),
    ("a // b", "a: str, b: int", "str"),
    ("xs - ys", "xs: list[int], ys: list[int]", "list[int]"),
])
def test_operations_python_itself_rejects_say_so(body, sig, ret):
    # Distinguished from "not modelled yet": CPython raises TypeError here,
    # and a fixit suggesting the fragment might grow would be misleading.
    _reject(_fn(body, sig, ret), "raises TypeError")


def test_undetermined_operand_type_fails_closed():
    # The inferencer is conservative; an operand it cannot type is rejected
    # rather than emitted and hoped for (what `**` already did).
    src = ("#@ ensures result >= 0\n"
           "def f(xs: list[int]) -> int:\n"
           "    return xs[0][0] + 1\n")
    _reject(src, "cannot determine the operand types|outside the slice-1 encoder")


def test_the_legitimate_cases_still_encode():
    assert "(a + b)" in _encode(_fn("a + b", "a: str, b: str"))
    assert "(a + b)" in _encode(_fn("a + b", "a: list[int], b: list[int]", "list[int]"))
    assert "(a + b)" in _encode(_fn("a + b", "a: int, b: int", "int"))
    assert "(a - b)" in _encode(_fn("a - b", "a: int, b: int", "int"))
    assert "PyMod(a, b)" in _encode(_fn("a % b", "a: int, b: int", "int"))


def test_empty_list_literal_takes_its_type_from_the_other_operand():
    # `[] + xs` encoded and verified before operands were type-checked here;
    # `_infer` cannot type a bare `[]`, so the fail-closed branch would have
    # rejected a concatenation the fragment has always modelled.
    assert "([] + xs)" in _encode(_fn("[] + xs", "xs: list[int]", "list[int]"))
    assert "(xs + [])" in _encode(_fn("xs + []", "xs: list[int]", "list[int]"))
    # and the type it borrows propagates, so nesting still works
    assert "(([] + xs) + ys)" in _encode(
        _fn("([] + xs) + ys", "xs: list[int], ys: list[int]", "list[int]"))


@pytest.mark.parametrize("body,sig,ret", [
    ("[] + []", "", "list[int]"),        # nothing supplies the element type
    ("[] + s", "s: str", "str"),         # Python: TypeError, list + str
    ("[] + n", "n: int", "int"),
    ("[] * 3", "", "list[int]"),         # the exception is `+` only
    ("[] - xs", "xs: list[int]", "list[int]"),
])
def test_empty_list_exception_does_not_leak(body, sig, ret):
    # The sibling types a bare `[]` only across `+`, and only against a
    # list; everything else stays fail-closed.
    _reject(_fn(body, sig, ret), "cannot determine the operand types")


# --- sidecar line mapping ------------------------------------------------------

def test_sidecar_locate_maps_stub_lines_to_the_files_own_lines(tmp_path):
    from veripy.backends.dafny.encoder import ProofSidecar, load_proof_sidecar

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == 0\ndef f() -> int:\n    return 0\n")
    (tmp_path / "m.proofs.dfy").write_text(
        "lemma A(x: int)\n  ensures x == x\n{\n}\n")
    sidecar = load_proof_sidecar(src)
    extent = 100  # pretend the generated stub ends here
    # The wrapper prepends a blank line and a header comment, so the file's
    # own line 1 sits at extent + header_lines. Derived, not assumed:
    assert sidecar.header_lines == 2
    assert sidecar.locate(extent + 2, extent) == (str(tmp_path / "m.proofs.dfy"), 1)
    assert sidecar.locate(extent + 3, extent) == (str(tmp_path / "m.proofs.dfy"), 2)
    # Lines at or before the stub's end are NOT the sidecar's.
    assert sidecar.locate(extent, extent) is None
    assert sidecar.locate(1, extent) is None
    # A file with no sidecar can never claim a line.
    assert ProofSidecar.empty().locate(extent + 5, extent) is None


def test_map_line_refuses_to_answer_past_the_generated_region():
    from veripy.backends.dafny.driver import _map_line

    line_map = {10: 3, 20: 7}
    # Inside the generated region: exact hit, then nearest-above (statements
    # span more lines than they are keyed at).
    assert _map_line(line_map, 20, 30) == 7
    assert _map_line(line_map, 25, 30) == 7
    # Past it, the nearest-above fallback would answer 7 -- the last Python
    # line encoded, which has nothing to do with a lemma in the sidecar.
    assert _map_line(line_map, 31, 30) is None
    assert _map_line(line_map, 99, 30) is None
    # Unbounded callers keep the old behaviour.
    assert _map_line(line_map, 99) == 7


def test_while_break_and_continue_lower_directly():
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result == n\n"
        "def f(n: int) -> int:\n"
        "    i = 0\n"
        "    while i < n:\n"
        "        #@ invariant 0 <= i <= n\n"
        "        #@ decreases n - i\n"
        "        if False:\n"
        "            continue\n"
        "        if False:\n"
        "            break\n"
        "        i = i + 1\n"
        "    return i\n"
    )
    dfy = _encode(src)
    assert "continue;" in dfy
    assert "break;" in dfy
    lines = dfy.splitlines()
    cont = next(i for i, ln in enumerate(lines) if ln.strip() == "continue;")
    # A while has no hidden index; continue must not invent a step.
    assert ":= " not in lines[cont - 1]


def test_range_for_continue_advances_the_index_before_continue():
    # The range-for lowering puts `i := i + 1` AFTER the body. A bare
    # Dafny `continue` would skip it and spin. The encoder must emit the
    # step, then continue.
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def skip_evens(n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        #@ invariant 0 <= i <= n\n"
        "        #@ invariant s >= 0\n"
        "        if i % 2 == 0:\n"
        "            continue\n"
        "        s = s + i\n"
        "    return s\n"
    )
    dfy = _encode(src)
    lines = dfy.splitlines()
    cont = next(i for i, ln in enumerate(lines) if ln.strip() == "continue;")
    assert lines[cont - 1].strip() == "i := i + 1;"
    assert sum(1 for ln in lines if ln.strip() == "i := i + 1;") >= 2


def test_foreach_continue_advances_the_snapshot_index():
    src = (
        "#@ ensures result >= 0\n"
        "def skip_neg(xs: list[int]) -> int:\n"
        "    s = 0\n"
        "    for x in xs:\n"
        "        #@ invariant s >= 0\n"
        "        if x < 0:\n"
        "            continue\n"
        "        s = s + x\n"
        "    return s\n"
    )
    dfy = _encode(src)
    lines = dfy.splitlines()
    cont = next(i for i, ln in enumerate(lines) if ln.strip() == "continue;")
    prev = lines[cont - 1].strip()
    assert prev.endswith("+ 1;") and ":=" in prev


def test_nested_while_continue_does_not_step_the_enclosing_for():
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        #@ invariant 0 <= i <= n\n"
        "        #@ invariant s >= 0\n"
        "        j = 0\n"
        "        while j < 1:\n"
        "            #@ invariant 0 <= j <= 1\n"
        "            #@ decreases 1 - j\n"
        "            if False:\n"
        "                continue\n"
        "            j = j + 1\n"
        "        s = s + i\n"
        "    return s\n"
    )
    dfy = _encode(src)
    lines = dfy.splitlines()
    cont = next(i for i, ln in enumerate(lines) if ln.strip() == "continue;")
    assert "i := i + 1;" not in lines[cont - 1]


def test_tuple_return_and_constant_index():
    src = (
        "#@ ensures result[0] == x\n"
        "#@ ensures result[1] == y\n"
        "def pair(x: int, y: int) -> tuple[int, int]:\n"
        "    return (x, y)\n"
    )
    dfy = _encode(src)
    assert "returns (result: (int, int))" in dfy
    assert "result := (x, y);" in dfy
    assert "result.0 == x" in dfy
    assert "result.1 == y" in dfy
    assert "result[PyIndex" not in dfy


def test_tuple_unpack_from_name_projects_components():
    src = (
        "#@ ensures result == p[0] + p[1]\n"
        "def add_pair(p: tuple[int, int]) -> int:\n"
        "    a, b = p\n"
        "    return a + b\n"
    )
    dfy = _encode(src)
    assert "var a, b := p.0, p.1;" in dfy
    assert "a, b := p;" not in dfy


def test_tuple_unpack_from_literal_stays_parallel():
    src = (
        "#@ ensures result == x + y\n"
        "def add(x: int, y: int) -> int:\n"
        "    a, b = x, y\n"
        "    return a + b\n"
    )
    dfy = _encode(src)
    assert "var a, b := x, y;" in dfy


def test_tuple_negative_index_wraps():
    src = (
        "#@ ensures result == p[1]\n"
        "def last(p: tuple[int, int]) -> int:\n"
        "    return p[-1]\n"
    )
    dfy = _encode(src)
    assert "result := p.1;" in dfy
    assert "p[PyIndex" not in dfy


def test_tuple_unpack_complex_rhs_binds_once():
    src = (
        "#@ ensures result == x + y\n"
        "def add(x: int, y: int) -> int:\n"
        "    a, b = (x + 1, y)\n"
        "    return a + b - 1\n"
    )
    dfy = _encode(src)
    # Literal RHS stays a parallel assignment of the elements, not one
    # Dafny tuple that would fail `a, b := (x + 1, y)`.
    assert "var a, b := (x + 1), y;" in dfy


def test_tuple_arity_mismatch_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(p: tuple[int, int, int]) -> int:\n"
        "    a, b = p\n"
        "    return a + b\n",
        "arity 3",
    )


def test_tuple_concat_rejected():
    _expect_encode_error(
        "#@ ensures result[0] == 0\n"
        "def f(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:\n"
        "    return a + b\n",
        "tuple concatenation",
    )


def test_tuple_one_elt_type_rejected():
    _expect_encode_error(
        "#@ ensures result == x\n"
        "def f(x: int) -> tuple[int]:\n"
        "    return (x,)\n",
        "2–8 elements",
    )


def test_tuple_variable_index_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(p: tuple[int, int], i: int) -> int:\n"
        "    return p[i]\n",
        "tuple index must be a constant",
    )


def test_nested_tuple_unpack_binds_projection_once():
    src = (
        "#@ ensures result == p[0][0] + p[0][1] + p[1]\n"
        "def f(p: tuple[tuple[int, int], int]) -> int:\n"
        "    a, b = p[0]\n"
        "    return a + b + p[1]\n"
    )
    dfy = _encode(src)
    assert "var tup := p.0;" in dfy
    assert "var a, b := tup.0, tup.1;" in dfy


def test_all_any_genexp_in_body_lowers_to_quantifiers():
    src = (
        "#@ ensures result == True or result == False\n"
        "def f(l: list[int]) -> bool:\n"
        "    return all(x > 0 for x in l)\n"
    )
    dfy = _encode(src)
    assert "forall x :: (x in l) ==> ((x > 0))" in dfy

    src = (
        "#@ ensures result == True or result == False\n"
        "def g(l: list[int]) -> bool:\n"
        "    return any(x == 0 for x in l)\n"
    )
    dfy = _encode(src)
    assert "exists x :: (x in l) && ((x == 0))" in dfy


def test_filtered_all_conjoins_the_guard():
    src = (
        "#@ ensures result == True or result == False\n"
        "def f(l: list[int]) -> bool:\n"
        "    return all(x > 0 for x in l if x % 2 == 0)\n"
    )
    dfy = _encode(src)
    assert "x in l && (PyMod(x, 2) == 0)" in dfy
    assert "==> ((x > 0))" in dfy


def test_all_of_int_genexp_rejected():
    _expect_encode_error(
        "#@ ensures result == True or result == False\n"
        "def f(l: list[int]) -> bool:\n"
        "    return all(x for x in l)\n",
        "bool-valued generator",
    )


def test_nested_list_comprehension_still_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(l: list[int]) -> list[int]:\n"
        "    return [x + y for x in l for y in l]\n",
        "single-generator",
    )


# --- walrus `:=` (always-evaluated positions) --------------------------------


def test_walrus_in_return_is_assignment_then_the_name():
    dfy = _encode(
        "#@ ensures result == n\n"
        "def f(n: int) -> int:\n"
        "    return (x := n)\n"
    )
    assert "var x := n;" in dfy
    assert "result := x;" in dfy


def test_walrus_in_if_test_assigns_before_the_if():
    dfy = _encode(
        "#@ ensures result == n or result == 0\n"
        "def f(n: int) -> int:\n"
        "    if (x := n) > 0:\n"
        "        return x\n"
        "    return 0\n"
    )
    assert "var x := n;" in dfy
    assert "if (x > 0)" in dfy


def test_walrus_in_while_test_rebinds_at_continue_and_loop_end():
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def countdown(n: int) -> int:\n"
        "    x = n\n"
        "    s = 0\n"
        "    while (x := x - 1) >= 0:\n"
        "        #@ invariant s >= 0\n"
        "        if x % 2 == 0:\n"
        "            continue\n"
        "        s = s + 1\n"
        "    return s\n"
    )
    dfy = _encode(src)
    assert "x := (x - 1);" in dfy
    assert "while (x >= 0)" in dfy
    lines = dfy.splitlines()
    cont = next(i for i, ln in enumerate(lines) if ln.strip() == "continue;")
    assert lines[cont - 1].strip() == "x := (x - 1);"
    # Initial eval + continue path + fall-through.
    assert sum(1 for ln in lines if ln.strip() == "x := (x - 1);") >= 3


def test_walrus_under_and_rejected():
    _expect_encode_error(
        "#@ ensures result == True or result == False\n"
        "def f(n: int) -> bool:\n"
        "    return n > 0 and (x := n) > 0\n",
        "short-circuit",
    )


def test_walrus_in_ifexp_branch_rejected():
    _expect_encode_error(
        "#@ ensures result == n or result == 0\n"
        "def f(n: int) -> int:\n"
        "    return (x := n) if n > 0 else 0\n",
        "conditional expression",
    )


def test_walrus_in_later_chained_comparison_rejected():
    _expect_encode_error(
        "#@ ensures result == True or result == False\n"
        "def f(a: int, b: int, c: int) -> bool:\n"
        "    return a < b < (x := c)\n",
        "chained comparison",
    )


def test_walrus_in_first_chained_operand_is_admitted():
    dfy = _encode(
        "#@ ensures result == True or result == False\n"
        "def f(a: int, b: int) -> bool:\n"
        "    return a < (x := b)\n"
    )
    assert "var x := b;" in dfy
    assert "a < x" in dfy


def test_walrus_in_comprehension_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(l: list[int]) -> list[int]:\n"
        "    return [y := x for x in l]\n",
        "comprehension",
    )


def test_walrus_in_spec_rejected():
    _expect_encode_error(
        "#@ ensures result == (n := n)\n"
        "def f(n: int) -> int:\n"
        "    return n\n",
        "spec clause",
    )


def test_walrus_parameter_rebind_rejected():
    _expect_encode_error(
        "#@ ensures result == n or result == 0\n"
        "def f(n: int) -> int:\n"
        "    return (n := n + 1)\n",
        "parameter rebinding",
    )


def test_fstring_lowers_to_concatenation():
    dfy = _encode(
        "#@ ensures result == \"hi \" + s\n"
        "def greet(s: str) -> str:\n"
        "    return f\"hi {s}\"\n"
    )
    assert '("hi " + s)' in dfy
    # A lone interpolation is identity on the str.
    ident = _encode(
        "#@ ensures result == s\n"
        "def ident(s: str) -> str:\n"
        "    return f\"{s}\"\n"
    )
    assert "result := s;" in ident


def test_fstring_literal_only_is_just_the_string():
    dfy = _encode(
        "#@ ensures result == \"hi\"\n"
        "def greet() -> str:\n"
        "    return f\"hi\"\n"
    )
    assert 'result := "hi";' in dfy


def test_fstring_empty_is_empty_string():
    dfy = _encode(
        "#@ ensures result == \"\"\n"
        "def empty() -> str:\n"
        "    return f\"\"\n"
    )
    assert 'result := "";' in dfy


def test_fstring_in_spec_matches_concatenation():
    dfy = _encode(
        "#@ ensures result == f\"hi {s}\"\n"
        "def greet(s: str) -> str:\n"
        "    return \"hi \" + s\n"
    )
    assert '("hi " + s)' in dfy


def test_fstring_int_interpolation_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(n: int) -> str:\n"
        "    return f\"{n}\"\n",
        "interpolating int",
    )


def test_fstring_bool_interpolation_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(b: bool) -> str:\n"
        "    return f\"{b}\"\n",
        "interpolating bool",
    )


def test_fstring_char_interpolation_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return f\"{s[0]}\"\n",
        "interpolating a character",
    )


def test_fstring_conversion_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return f\"{s!r}\"\n",
        "f-string conversions",
    )


def test_fstring_format_spec_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return f\"{s:>10}\"\n",
        "f-string format specs",
    )


# --- small math subset (gcd / factorial / isqrt) --------------------------------


def test_math_gcd_lowers_to_pygcd():
    src = (
        "import math\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def g(a: int, b: int) -> int:\n"
        "    return math.gcd(a, b)\n"
    )
    dfy = _encode(src)
    assert "PyGcd(a, b)" in dfy
    assert "import math" not in dfy  # recorded, not emitted


def test_from_math_import_factorial_lowers():
    src = (
        "from math import factorial\n"
        "\n"
        "#@ requires 0 <= n <= 12\n"
        "#@ ensures result >= 1\n"
        "def f(n: int) -> int:\n"
        "    return factorial(n)\n"
    )
    dfy = _encode(src)
    assert "PyFact(n)" in dfy


def test_math_aliases_resolve():
    src = (
        "import math as M\n"
        "from math import gcd as g, isqrt as root\n"
        "\n"
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int, n: int) -> int:\n"
        "    return M.gcd(a, b) + g(a, b) + root(n)\n"
    )
    dfy = _encode(src)
    assert "PyGcd(a, b)" in dfy
    assert "PyIsqrt(n)" in dfy
    method = dfy.split("method f(")[1]
    assert method.count("PyGcd(a, b)") == 2


def test_math_sqrt_rejected_as_ieee_float():
    src = (
        "import math\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(x: int) -> int:\n"
        "    return math.sqrt(x)\n"
    )
    _expect_encode_error(src, "IEEE float is outside the fragment")


def test_from_math_import_sqrt_rejected_as_ieee_float():
    src = (
        "from math import sqrt\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(x: int) -> int:\n"
        "    return sqrt(x)\n"
    )
    _expect_encode_error(src, "IEEE float is outside the fragment")


def test_math_gcd_three_args_rejected():
    src = (
        "import math\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int, c: int) -> int:\n"
        "    return math.gcd(a, b, c)\n"
    )
    _expect_encode_error(src, "exactly two ints")


def test_unimported_gcd_is_outside():
    src = (
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    _expect_encode_error(src, "outside the slice")


def test_from_math_import_gcd_does_not_shadow_as_builtin():
    # gcd must NOT be in _ENCODED_BUILTINS: that set rejects `from math
    # import prod as sum`. Importing gcd has to resolve, not bounce.
    src = (
        "from math import gcd\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    dfy = _encode(src)
    assert "PyGcd(a, b)" in dfy


def test_conditional_math_import_does_not_lower():
    # A nested import is not guaranteed to run; lowering gcd to PyGcd
    # would verify CPython behavior the source does not have.
    src = (
        "if True:\n"
        "    from math import gcd\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    _expect_encode_error(src, "outside the slice")


def test_rebound_math_import_does_not_lower():
    # A later module-level Store replaces the imported function; the
    # call is no longer math.gcd.
    src = (
        "from math import gcd\n"
        "gcd = 0\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    _expect_encode_error(src, "outside the slice")


def test_deleted_math_import_does_not_lower():
    # `del gcd` unbinds the name; CPython raises NameError, so lowering
    # to PyGcd would verify a result the source cannot produce.
    src = (
        "from math import gcd\n"
        "del gcd\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    _expect_encode_error(src, "outside the slice")


def test_math_attribute_assignment_does_not_lower():
    # `math.gcd = …` replaces the function on the module; lowering the
    # later call to PyGcd would verify CPython's replacement instead.
    src = (
        "import math\n"
        "math.gcd = abs\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return math.gcd(a, b)\n"
    )
    _expect_encode_error(src, "method calls are outside")


def test_math_attribute_deletion_does_not_lower():
    src = (
        "import math\n"
        "del math.gcd\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return math.gcd(a, b)\n"
    )
    _expect_encode_error(src, "method calls are outside")


def test_math_name_copy_still_lowers():
    src = (
        "import math\n"
        "m = math\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return m.gcd(a, b) + math.gcd(a, b)\n"
    )
    dfy = _encode(src)
    method = dfy.split("method f(")[1]
    assert method.count("PyGcd(a, b)") == 2


def test_math_alias_copy_attribute_assignment_does_not_lower():
    # `m = math; m.gcd = …` mutates the shared module object, so
    # `math.gcd` is the replacement too.
    src = (
        "import math\n"
        "m = math\n"
        "m.gcd = abs\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return math.gcd(a, b)\n"
    )
    _expect_encode_error(src, "method calls are outside")


def test_second_import_alias_attribute_assignment_does_not_lower():
    src = (
        "import math\n"
        "import math as M\n"
        "M.gcd = abs\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return math.gcd(a, b)\n"
    )
    _expect_encode_error(src, "method calls are outside")


def test_from_import_survives_alias_module_mutation():
    # `from math import gcd` snapshots the function; mutating the module
    # through an alias does not rebind the local.
    src = (
        "from math import gcd\n"
        "import math\n"
        "m = math\n"
        "m.gcd = abs\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    assert "PyGcd(a, b)" in _encode(src)


def test_unpacked_math_alias_attribute_assignment_does_not_lower():
    src = (
        "import math\n"
        "m, other = math, 0\n"
        "m.gcd = abs\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return math.gcd(a, b)\n"
    )
    _expect_encode_error(src, "method calls are outside")


def test_wildcard_import_does_not_keep_math_binding():
    # `from other import *` may rebind gcd; keeping the math table entry
    # would lower CPython's replacement to PyGcd.
    src = (
        "from math import gcd\n"
        "from other import *\n"
        "\n"
        "#@ ensures result >= 0\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    _expect_encode_error(src, "outside the slice")


# --- str methods (join / split / find / startswith / replace / strip) ------


def test_str_join_lowers_to_pystrjoin():
    dfy = _encode(
        "#@ ensures result == \"xay\"\n"
        "def glue() -> str:\n"
        "    return \"a\".join([\"x\", \"y\"])\n"
    )
    assert "PyStrJoin(\"a\", [\"x\", \"y\"])" in dfy


def test_str_join_empty_list():
    dfy = _encode(
        "#@ ensures result == \"\"\n"
        "def empty() -> str:\n"
        "    return \"\".join([])\n"
    )
    assert "PyStrJoin(\"\", [])" in dfy


def test_str_split_lowers_to_pystrsplit():
    dfy = _encode(
        "#@ ensures len(result) >= 1\n"
        "def parts(s: str) -> list[str]:\n"
        "    return s.split(\",\")\n"
    )
    assert "PyStrSplit(s, \",\")" in dfy


def test_str_find_lowers_to_pystrfind():
    dfy = _encode(
        "#@ ensures result == -1 or result >= 0\n"
        "def loc(s: str, sub: str) -> int:\n"
        "    return s.find(sub)\n"
    )
    assert "PyStrFind(s, sub)" in dfy


def test_str_startswith_endswith_lower():
    dfy = _encode(
        "#@ ensures result == True or result == False\n"
        "def pref(s: str, p: str) -> bool:\n"
        "    return s.startswith(p)\n"
        "\n"
        "#@ ensures result == True or result == False\n"
        "def suff(s: str, t: str) -> bool:\n"
        "    return s.endswith(t)\n"
    )
    assert "PyStrStartsWith(s, p)" in dfy
    assert "PyStrEndsWith(s, t)" in dfy


def test_str_replace_and_strip_lower():
    dfy = _encode(
        "#@ ensures len(result) >= 0\n"
        "def swapped(s: str) -> str:\n"
        "    return s.replace(\"a\", \"b\")\n"
        "\n"
        "#@ ensures len(result) >= 0\n"
        "def trimmed(s: str) -> str:\n"
        "    return s.strip(\" \")\n"
        "\n"
        "#@ ensures len(result) >= 0\n"
        "def left(s: str) -> str:\n"
        "    return s.lstrip(\"x\")\n"
        "\n"
        "#@ ensures len(result) >= 0\n"
        "def right(s: str) -> str:\n"
        "    return s.rstrip(\"x\")\n"
    )
    assert "PyStrReplace(s, \"a\", \"b\")" in dfy
    assert "PyStrStrip(s, \" \")" in dfy
    assert "PyStrLStrip(s, \"x\")" in dfy
    assert "PyStrRStrip(s, \"x\")" in dfy


def test_str_noarg_split_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> list[str]:\n"
        "    return s.split()\n",
        "pass an explicit sep",
    )


def test_str_noarg_strip_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return s.strip()\n",
        "pass an explicit chars",
    )


def test_str_lower_rejected_as_unicode_table():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return s.lower()\n",
        "silent ASCII approximation",
    )


def test_str_upper_rejected_as_unicode_table():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return s.upper()\n",
        "Unicode-table",
    )


def test_str_split_maxsplit_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> list[str]:\n"
        "    return s.split(\",\", 1)\n",
        "maxsplit",
    )


def test_str_split_empty_sep_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> list[str]:\n"
        "    return s.split(\"\")\n",
        "empty sep",
    )


def test_str_startswith_tuple_rejected():
    _expect_encode_error(
        "#@ ensures result == True or result == False\n"
        "def f(s: str) -> bool:\n"
        "    return s.startswith((\"a\", \"b\"))\n",
        "tuple of prefixes",
    )


def test_str_replace_count_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return s.replace(\"a\", \"b\", 1)\n",
        "count",
    )


def test_str_replace_empty_old_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> str:\n"
        "    return s.replace(\"\", \"-\")\n",
        "empty old",
    )


def test_str_method_on_non_str_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return xs.find(1)\n",
        "not str",
    )


def test_str_method_keywords_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(s: str) -> list[str]:\n"
        "    return s.split(sep=\",\")\n",
        "keyword arguments",
    )


def test_append_statement_still_lowers():
    dfy = _encode(APPEND_OK)
    assert "out := out + [0];" in dfy


# --- sorted() on list[int] ------------------------------------------------------


def test_sorted_encodes_to_pysorted_in_spec_and_code():
    src = (
        "#@ ensures result == sorted(xs)\n"
        "def f(xs: list[int]) -> list[int]:\n"
        "    return sorted(xs)\n"
    )
    assert _encode(src).count("PySorted(xs)") == 2


def test_sorted_rejects_key():
    _expect_encode_error(
        "#@ ensures result == xs\n"
        "def f(xs: list[int]) -> list[int]:\n"
        "    return sorted(xs, key=abs)\n",
        "key=/reverse=",
    )


def test_sorted_rejects_list_str():
    _expect_encode_error(
        "#@ ensures result == xs\n"
        "def f(xs: list[str]) -> list[str]:\n"
        "    return sorted(xs)\n",
        "list[int]",
    )


def test_parameter_shadowing_sorted_rejected():
    src = (
        "#@ ensures result == 0\n"
        "def h(sorted: int) -> int:\n"
        "    return sorted\n"
    )
    with pytest.raises(EncodeError, match="shadows a builtin"):
        _encode(src)


def test_str_int_lowers_to_pyinttostr():
    dfy = _encode(
        "#@ ensures result == str(n)\n"
        "def show(n: int) -> str:\n"
        "    return str(n)\n"
    )
    assert "PyIntToStr(n)" in dfy
    assert "returns (result: string)" in dfy

def test_int_str_lowers_to_pystrtoint():
    dfy = _encode(
        "#@ requires s == \"12\"\n"
        "#@ ensures result == int(s)\n"
        "def parse(s: str) -> int:\n"
        "    return int(s)\n"
    )
    assert "PyStrToInt(s)" in dfy
    assert "returns (result: int)" in dfy

def test_str_of_bool_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(flag: bool) -> str:\n"
        "    return str(flag)\n",
        "bool is a disjoint sort",
    )

def test_str_of_list_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(xs: list[int]) -> str:\n"
        "    return str(xs)\n",
        "str(int) only",
    )

def test_int_of_int_rejected():
    _expect_encode_error(
        "#@ ensures result == n\n"
        "def f(n: int) -> int:\n"
        "    return int(n)\n",
        "parses a digit string",
    )

def test_int_with_base_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(s: str) -> int:\n"
        "    return int(s, 10)\n",
        "parses a digit string",
    )

def test_int_keyword_rejected():
    _expect_encode_error(
        "#@ ensures result >= 0\n"
        "def f(s: str) -> int:\n"
        "    return int(s, base=10)\n",
        "keyword arguments",
    )

def test_int_illformed_literal_rejected():
    for lit in ('"+12"', '" 1"', '"1_2"', '""', '"-"'):
        _expect_encode_error(
            "#@ ensures result >= 0\n"
            f"def f() -> int:\n"
            f"    return int({lit})\n",
            "strip whitespace / drop `_`/`+`",
        )

def test_int_annotation_is_not_shadowing():
    # `n: int` is a type, not a binding of the builtin.
    dfy = _encode(
        "#@ ensures result == n\n"
        "def f(n: int) -> int:\n"
        "    return n\n"
    )
    assert "method f(n: int) returns (result: int)" in dfy

def test_fstring_int_interpolation_still_rejected():
    _expect_encode_error(
        "#@ ensures len(result) >= 0\n"
        "def f(n: int) -> str:\n"
        "    return f\"{n}\"\n",
        "interpolating int",
    )


# --- str methods (join / split / find / startswith / replace / strip) ------
