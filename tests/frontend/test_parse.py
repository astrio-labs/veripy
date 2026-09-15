import pytest

from veripy.frontend.extract import parse_source
from veripy.frontend.parse import SpecError, desugar


def test_desugar_forall():
    assert desugar("forall i in range(n) :: xs[i] >= 0") == \
        "all((xs[i] >= 0) for i in (range(n)))"


def test_desugar_exists():
    assert desugar("exists v in xs :: v == target") == \
        "any((v == target) for v in (xs))"


def test_desugar_implication():
    assert desugar("x > 0 ==> y > 0") == "(not (x > 0)) or (y > 0)"


def test_desugar_implication_right_assoc():
    assert desugar("a ==> b ==> c") == "(not (a)) or ((not (b)) or (c))"


def test_desugar_iff():
    assert desugar("x > 0 <==> y > 0") == "bool(x > 0) == bool(y > 0)"


def test_desugar_iff_binds_loosest():
    got = desugar("a ==> b <==> c")
    assert got == "bool((not (a)) or (b)) == bool(c)"


def test_desugar_iff_with_quantifier_operand():
    got = desugar("done <==> forall i in range(n) :: xs[i] >= 0")
    assert got == "bool(done) == bool(all((xs[i] >= 0) for i in (range(n))))"


def test_desugar_multi_binder_with_implication_body():
    got = desugar("forall i in r, j in s :: p(i) ==> q(j)")
    assert got == "all(((not (p(i))) or (q(j))) for i in (r) for j in (s))"


def test_desugar_nested_quantifier():
    got = desugar("forall i in r :: exists j in s :: i < j")
    assert got == "all((any((i < j) for j in (s))) for i in (r))"


def test_desugar_parenthesized_quantifier():
    got = desugar("(forall i in r :: p(i)) and q")
    assert got == "(all((p(i)) for i in (r))) and q"


def test_desugar_plain_python_unchanged():
    assert desugar("lo <= result <= hi") == "lo <= result <= hi"


def test_desugar_missing_double_colon():
    with pytest.raises(SpecError, match="'::'"):
        desugar("forall i in r xs")


def test_desugar_bad_binder():
    with pytest.raises(SpecError, match="binder"):
        desugar("forall i :: xs[i] >= 0")


SRC_OK = '''
#@ verified
#@ requires lo <= hi
#@ ensures lo <= result <= hi
def clamp(x: int, lo: int, hi: int) -> int:
    if x < lo:
        return lo
    return min(x, hi)
'''


def test_parse_source_ok():
    specs = parse_source(SRC_OK)
    assert len(specs.functions) == 1
    fn = specs.functions[0]
    assert fn.name == "clamp"
    assert fn.verified
    assert not fn.errors
    assert [c.kind for c in fn.clauses] == ["verified", "requires", "ensures"]


def test_unknown_name_rejected():
    src = "#@ requires banana > 0\ndef f(x: int) -> int:\n    return x\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert fn.errors and "banana" in fn.errors[0].error


def test_result_only_in_ensures():
    src = "#@ requires result > 0\ndef f(x: int) -> int:\n    return x\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert fn.errors and "result" in fn.errors[0].error


def test_old_only_in_ensures():
    src = "#@ requires old(x) > 0\ndef f(x: int) -> int:\n    return x\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert fn.errors and "old" in fn.errors[0].error


def test_old_collected():
    src = "#@ ensures result == old(x) + 1\ndef f(x: int) -> int:\n    return x + 1\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert not fn.errors
    assert fn.clauses[0].old_names == ("x",)


def test_invariant_recorded_inside_loop():
    src = (
        "#@ requires n >= 0\n"
        "def f(n: int) -> int:\n"
        "    total = 0\n"
        "    for i in range(n):\n"
        "        #@ invariant total >= 0\n"
        "        total += i\n"
        "    return total\n"
    )
    specs = parse_source(src)
    (fn,) = specs.functions
    assert not fn.errors
    assert [c.kind for c in fn.clauses] == ["requires", "invariant"]


def test_invariant_in_header_rejected():
    src = "#@ invariant x > 0\ndef f(x: int) -> int:\n    return x\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert fn.errors and "loop body" in fn.errors[0].error


def test_orphan_comment_reported():
    src = "#@ requires x > 0\n\n\ndef f(x: int) -> int:\n    return x\n"
    specs = parse_source(src)
    assert specs.orphans and "not attached" in specs.orphans[0].error


def test_unspecced_variadic_sibling_does_not_abort():
    src = (
        "def helper(*args, **kwargs):\n"
        "    return args, kwargs\n"
        "\n"
        "\n"
        "#@ requires x > 0\n"
        "def f(x: int) -> int:\n"
        "    return x\n"
    )
    specs = parse_source(src)
    assert [fn.name for fn in specs.functions] == ["f"]
    assert not specs.functions[0].errors


def test_specced_variadic_reports_error():
    src = "#@ ensures result >= 0\ndef f(*args) -> int:\n    return len(args)\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert any(c.error and "outside the fragment" in c.error for c in fn.clauses)


def test_reserved_param_name_rejected():
    src = "#@ ensures result >= 0\ndef f(result: int) -> int:\n    return result\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert any(c.error and "reserved" in c.error for c in fn.clauses)


def test_reserved_old_param_rejected():
    src = "#@ ensures result >= 0\ndef f(OLD: int) -> int:\n    return OLD\n"
    specs = parse_source(src)
    (fn,) = specs.functions
    assert any(c.error and "reserved" in c.error for c in fn.clauses)
