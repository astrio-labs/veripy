from veripy.frontend.conformance import aggregate, survey_paths, survey_source


def _fires(src: str, qualname: str | None = None) -> set[str]:
    report = survey_source(src)
    fns = [f for f in report.functions if qualname is None or f.qualname == qualname]
    return {fire.rule for fn in fns for fire in fn.fires}


def test_pure_function_accepted():
    src = (
        "def gcd(a: int, b: int) -> int:\n"
        "    while b != 0:\n"
        "        a, b = b, a % b\n"
        "    return a\n"
    )
    report = survey_source(src)
    (fn,) = report.functions
    assert fn.accepted


def test_modeled_method_calls_accepted():
    src = (
        "def dedupe(xs: list[int]) -> list[int]:\n"
        "    out: list[int] = []\n"
        "    for x in xs:\n"
        "        if x not in out:\n"
        "            out.append(x)\n"
        "    return out\n"
    )
    (fn,) = survey_source(src).functions
    assert fn.accepted


def test_try_and_raise_fire():
    src = (
        "def f(x: int) -> int:\n"
        "    try:\n"
        "        return x\n"
        "    except ValueError:\n"
        "        raise\n"
    )
    assert {"X-TRY", "X-RAISE"} <= _fires(src)


def test_float_literal_fires():
    assert "T-FLOAT" in _fires("def f() -> float:\n    return 0.5\n")


def test_float_call_fires():
    assert "T-FLOAT" in _fires("def f(x: int):\n    return float(x)\n")


def test_bool_constant_does_not_fire_float():
    assert "T-FLOAT" not in _fires("def f() -> bool:\n    return True\n")


def test_reflection_fires():
    assert "F-REFL" in _fires("def f(o, n: str):\n    return getattr(o, n)\n")


def test_eval_fires():
    assert "F-EVAL" in _fires("def f(s: str):\n    return eval(s)\n")


def test_decorator_fires():
    src = "@staticmethod\ndef f(x: int) -> int:\n    return x\n"
    assert "X-DECOR" in _fires(src)


def test_unknown_method_fires_u_method():
    assert "U-METHOD" in _fires("def f(o):\n    return o.frobnicate()\n")


def test_unknown_call_fires_u_call():
    assert "U-CALL" in _fires("def f(x: int):\n    return mystery(x)\n")


def test_module_local_call_accepted():
    src = (
        "def helper(x: int) -> int:\n"
        "    return x + 1\n"
        "\n"
        "def f(x: int) -> int:\n"
        "    return helper(x)\n"
    )
    assert _fires(src, "f") == set()


def test_imported_name_call_accepted_as_module_name():
    src = (
        "from math import gcd\n"
        "\n"
        "def f(a: int, b: int) -> int:\n"
        "    return gcd(a, b)\n"
    )
    assert _fires(src, "f") == set()


def test_nested_def_fires_and_gets_own_report():
    src = (
        "def outer(x: int) -> int:\n"
        "    def inner(y: int) -> int:\n"
        "        return y + 1\n"
        "    return inner(x)\n"
    )
    report = survey_source(src)
    names = {fn.qualname for fn in report.functions}
    assert names == {"outer", "outer.inner"}
    assert "X-NESTED" in _fires(src, "outer")
    assert _fires(src, "outer.inner") == set()


def test_method_of_inheriting_class_fires():
    src = (
        "class A(Base):\n"
        "    def m(self) -> int:\n"
        "        return 1\n"
    )
    assert "X-CLASS-INHERIT" in _fires(src)


def test_plain_class_method_no_inherit_fire():
    src = (
        "class A:\n"
        "    def m(self) -> int:\n"
        "        return 1\n"
    )
    assert "X-CLASS-INHERIT" not in _fires(src)


def test_dunder_method_fires():
    src = (
        "class A:\n"
        "    def __eq__(self, other) -> bool:\n"
        "        return True\n"
    )
    assert "X-DUNDER-DEF" in _fires(src)


def test_init_is_not_a_dunder_fire():
    src = (
        "class A:\n"
        "    def __init__(self) -> None:\n"
        "        pass\n"
    )
    assert "X-DUNDER-DEF" not in _fires(src)


def test_type_ignore_comment_fires():
    src = "def f(x: int) -> int:\n    return x  # type: ignore\n"
    assert "F-IGNORE" in _fires(src)


def test_is_none_allowed_is_object_fires():
    assert "T-IS" not in _fires("def f(x):\n    return x is None\n")
    assert "T-IS" in _fires("def f(x, y):\n    return x is y\n")


def test_yield_fires():
    assert "X-YIELD" in _fires("def f(n: int):\n    for i in range(n):\n        yield i\n")


def test_mutable_default_fires():
    assert "T-MUT-DEFAULT" in _fires("def f(xs=[]):\n    return xs\n")


def test_attr_store_fires():
    src = (
        "class A:\n"
        "    def __init__(self) -> None:\n"
        "        self.x = 1\n"
    )
    assert "X-ATTR-STORE" in _fires(src)


def test_fstring_format_spec_still_fires():
    src = "def f(x: int) -> str:\n    return f'{x:d}'\n"
    assert "T-FSTRING" in _fires(src)


def test_fstring_conversion_still_fires():
    src = "def f(s: str) -> str:\n    return f'{s!r}'\n"
    assert "T-FSTRING" in _fires(src)


def test_bare_str_fstring_does_not_fire():
    # Admitted as concatenation when the interpolation is str-typed.
    src = "def f(s: str) -> str:\n    return f'hi {s}'\n"
    assert "T-FSTRING" not in _fires(src)


def test_bare_int_fstring_still_fires():
    # Encoder rejects `f"{n}"` for `n: int`; the survey can see the
    # annotation even without an inferencer.
    src = "def f(n: int) -> str:\n    return f'{n}'\n"
    assert "T-FSTRING" in _fires(src)


def test_aggregate_counts():
    src = (
        "def good(x: int) -> int:\n"
        "    return x + 1\n"
        "\n"
        "def bad(x: int):\n"
        "    raise ValueError(x)\n"
    )
    stats = aggregate([survey_source(src)])
    assert stats["functions"] == 2
    assert stats["accepted"] == 1
    assert stats["rule_counts"]["X-RAISE"] == 1


def test_syntax_error_reported_not_raised():
    report = survey_source("def f(:\n")
    assert report.error is not None


# --- regressions from the adversarial review (2026-08-11) -------------------


def test_aliased_cast_and_importlib_fire():
    src = (
        "from importlib import import_module\n"
        "from typing import cast as c\n"
        "\n"
        "def load(name: str) -> object:\n"
        "    return c(object, import_module(name))\n"
    )
    fires = _fires(src)
    assert "F-CAST" in fires
    assert "F-DYNIMPORT" in fires


def test_rebound_eval_fires():
    src = "def f(s: str):\n    run = eval\n    return run(s)\n"
    assert "F-EVAL" in _fires(src)


def test_sys_modules_real_shapes_fire():
    src = (
        "import sys\n"
        "def unload(name: str) -> None:\n"
        "    sys.modules.pop(name)\n"
        "def peek(name: str):\n"
        "    return sys.modules[name]\n"
    )
    assert "F-DYNIMPORT" in _fires(src, "unload")
    assert "F-DYNIMPORT" in _fires(src, "peek")


def test_true_division_fires():
    assert "T-DIV" in _fires("def mean(xs: list[int]):\n    return sum(xs) / len(xs)\n")
    assert "T-DIV" in _fires("def f(a: int, b: int):\n    a /= b\n    return a\n")


def test_pow_and_matmul_fire_u_op():
    assert "U-OP" in _fires("def f(a: int, b: int):\n    return a ** b\n")
    assert "U-OP" in _fires("def g(a, b):\n    return a @ b\n")


def test_float_in_default_and_annotation_fires():
    assert "T-FLOAT" in _fires("def f(eps=1e-9):\n    return eps\n")
    assert "T-FLOAT" in _fires("def f(x: float) -> int:\n    return 0\n")


def test_eval_in_default_fires():
    assert "F-EVAL" in _fires("def f(x=eval('1')):\n    return x\n")


def test_metaclass_fires():
    src = "class A(metaclass=type):\n    def m(self):\n        return 1\n"
    assert "F-METACLASS" in _fires(src)


def test_class_decorator_fires_but_dataclass_allowed():
    src = "@register\nclass A:\n    def m(self):\n        return 1\n"
    assert "X-CLASS-DECOR" in _fires(src)
    src_ok = (
        "from dataclasses import dataclass\n"
        "@dataclass(frozen=True)\n"
        "class P:\n"
        "    def m(self):\n"
        "        return 1\n"
    )
    assert "X-CLASS-DECOR" not in _fires(src_ok)


def test_bytes_and_complex_fire_u_const():
    assert "U-CONST" in _fires("def f():\n    return b'x'\n")
    assert "U-CONST" in _fires("def f():\n    return 1j\n")


def test_global_container_mutation_fires():
    src = (
        "CACHE: list[int] = []\n"
        "TABLE: dict[str, int] = {}\n"
        "def put(x: int, k: str) -> None:\n"
        "    CACHE.append(x)\n"
        "    TABLE[k] = x\n"
    )
    fires = [f.rule for fn in survey_source(src).functions for f in fn.fires]
    assert fires.count("T-GLOBAL") == 2


def test_local_shadow_of_global_no_fire():
    src = (
        "CACHE = []\n"
        "def f(x: int):\n"
        "    CACHE = []\n"
        "    CACHE.append(x)\n"
        "    return CACHE\n"
    )
    assert "T-GLOBAL" not in _fires(src)


def test_for_target_attribute_store_fires():
    src = "def f(o, xs):\n    for o.x in xs:\n        pass\n"
    assert "X-ATTR-STORE" in _fires(src)


def test_def_inside_module_level_try_is_scored():
    src = (
        "try:\n"
        "    import fast\n"
        "except ImportError:\n"
        "    def fallback(x: int) -> int:\n"
        "        return x\n"
    )
    names = {fn.qualname for fn in survey_source(src).functions}
    assert "fallback" in names


def test_def_under_module_if_visible_to_callers():
    src = (
        "import sys\n"
        "if sys.version_info >= (3, 12):\n"
        "    def helper(x: int) -> int:\n"
        "        return x\n"
        "\n"
        "def f(x: int) -> int:\n"
        "    return helper(x)\n"
    )
    assert "U-CALL" not in _fires(src, "f")


def test_type_ignore_attributed_once_to_innermost():
    src = (
        "def outer(x: int):\n"
        "    def inner(y: int):\n"
        "        return y  # type: ignore\n"
        "    return inner(x)\n"
    )
    report = survey_source(src)
    count = sum(1 for fn in report.functions for f in fn.fires if f.rule == "F-IGNORE")
    assert count == 1


def test_lambda_param_is_not_a_parent_local():
    src = (
        "def f(xs):\n"
        "    g = lambda q: q + 1\n"
        "    return q(xs)\n"
    )
    assert "U-CALL" in _fires(src)


def test_star_import_counted_once_at_file_level():
    src = (
        "from os.path import *\n"
        "def a() -> int:\n"
        "    return 1\n"
        "def b() -> int:\n"
        "    return 2\n"
    )
    report = survey_source(src)
    assert all(fn.accepted for fn in report.functions)
    stars = [f for f in report.file_fires if f.rule == "U-IMPORT-STAR"]
    assert len(stars) == 1


def test_decorators_fire_per_decorator():
    src = "@a\n@b\ndef f():\n    return 1\n"
    (fn,) = survey_source(src).functions
    assert sum(1 for f in fn.fires if f.rule == "X-DECOR") == 2


def test_async_fires_once_even_with_awaits():
    src = "async def f(x):\n    await x\n    await x\n"
    (fn,) = survey_source(src).functions
    assert sum(1 for f in fn.fires if f.rule == "X-ASYNC") == 1


def test_builtins_aliased_eval_fires():
    src = (
        "from builtins import eval as run\n"
        "def f(s: str):\n"
        "    return run(s)\n"
    )
    assert "F-EVAL" in _fires(src)


def test_lambda_calling_own_param_accepted():
    src = (
        "def f(v: int) -> int:\n"
        "    g = lambda cb: cb(v)\n"
        "    return g(abs)\n"
    )
    (fn,) = survey_source(src).functions
    assert fn.accepted, [f.rule for f in fn.fires]


def test_lambda_param_shadowing_does_not_leak_out():
    # A call to the lambda's parameter name from OUTSIDE the lambda must
    # still fire U-CALL (regression guard for the earlier scope fix).
    src = (
        "def f(xs):\n"
        "    g = lambda q: q + 1\n"
        "    return q(xs)\n"
    )
    assert "U-CALL" in _fires(src)


def test_module_qualified_builtins_fire():
    src = (
        "import builtins\n"
        "def f(s: str, o, n: str):\n"
        "    x = builtins.eval(s)\n"
        "    return builtins.getattr(o, n), x\n"
    )
    fires = _fires(src)
    assert "F-EVAL" in fires
    assert "F-REFL" in fires


def test_rebound_qualified_builtin_fires():
    src = (
        "import builtins as b\n"
        "def f(s: str):\n"
        "    run = b.eval\n"
        "    return run(s)\n"
    )
    assert "F-EVAL" in _fires(src)


def test_overlapping_paths_counted_once(tmp_path):
    (tmp_path / "m.py").write_text("def f(x: int) -> int:\n    return x\n")
    reports = survey_paths([tmp_path, tmp_path / "m.py"])
    stats = aggregate(reports)
    assert stats["files"] == 1
    assert stats["functions"] == 1


def test_admitted_assert_does_not_fire():
    src = (
        "def f(n: int) -> int:\n"
        "    assert n >= 0\n"
        "    return n\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_nonliteral_message_still_fires():
    src = (
        "def f(n: int) -> int:\n"
        "    assert n >= 0, str(n)\n"
        "    return n\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_int_name_still_fires():
    src = (
        "def f(n: int) -> int:\n"
        "    assert n\n"
        "    return n\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_annotated_local_still_fires():
    src = (
        "def f() -> int:\n"
        "    n: int = 1\n"
        "    assert n\n"
        "    return n\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_inferred_int_local_still_fires():
    src = (
        "def f() -> int:\n"
        "    n = 1\n"
        "    assert n\n"
        "    return n\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_bool_name_does_not_fire():
    src = (
        "def f(flag: bool) -> bool:\n"
        "    assert flag\n"
        "    return flag\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_int_binop_still_fires():
    src = (
        "def f(n: int) -> int:\n"
        "    assert n + 1\n"
        "    return n\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_negated_int_still_fires():
    src = (
        "def f(n: int) -> int:\n"
        "    assert -n\n"
        "    return n\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_len_still_fires():
    src = (
        "def f(xs: list[int]) -> int:\n"
        "    assert len(xs)\n"
        "    return 0\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_list_name_does_not_fire():
    # Encoder admits list/str truthiness as `|xs| != 0`.
    src = (
        "def f(xs: list[int]) -> list[int]:\n"
        "    assert xs\n"
        "    return xs\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_list_int_index_still_fires():
    src = (
        "def f(xs: list[int]) -> int:\n"
        "    assert xs[0]\n"
        "    return 0\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_ifexp_int_still_fires():
    src = (
        "def f(n: int, m: int, flag: bool) -> int:\n"
        "    assert n if flag else m\n"
        "    return n\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_list_str_index_does_not_fire():
    # Element is str; encoder admits str truthiness as emptiness.
    src = (
        "def f(xs: list[str]) -> str:\n"
        "    assert xs[0]\n"
        "    return xs[0]\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_nested_list_int_index_still_fires():
    src = (
        "def f(xs: list[list[int]]) -> int:\n"
        "    assert xs[0][0]\n"
        "    return 0\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_nested_list_str_index_does_not_fire():
    # Element is str; encoder admits str truthiness as emptiness.
    src = (
        "def f(xs: list[list[str]]) -> str:\n"
        "    assert xs[0][0]\n"
        "    return xs[0][0]\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_list_of_list_index_does_not_fire():
    # xs[0] is list; encoder admits list truthiness as emptiness.
    src = (
        "def f(xs: list[list[int]]) -> int:\n"
        "    assert xs[0]\n"
        "    return 0\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_list_tuple_index_still_fires():
    src = (
        "def f(xs: list[tuple[int, int]]) -> int:\n"
        "    assert xs[0]\n"
        "    return 0\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_tuple_int_index_still_fires():
    src = (
        "def f(p: tuple[int, int]) -> int:\n"
        "    assert p[0]\n"
        "    return p[0]\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_tuple_str_index_does_not_fire():
    src = (
        "def f(p: tuple[str, str]) -> str:\n"
        "    assert p[0]\n"
        "    return p[0]\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_tuple_literal_still_fires():
    src = (
        "def f() -> int:\n"
        "    assert (1, 2)\n"
        "    return 0\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_inferred_list_int_index_still_fires():
    src = (
        "def f() -> int:\n"
        "    xs = [1, 2, 3]\n"
        "    assert xs[0]\n"
        "    return 0\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_inferred_list_str_index_does_not_fire():
    src = (
        "def f() -> str:\n"
        "    xs = [\"a\", \"b\"]\n"
        "    assert xs[0]\n"
        "    return xs[0]\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_inferred_list_name_does_not_fire():
    # Encoder admits list truthiness as `|xs| != 0`.
    src = (
        "def f() -> int:\n"
        "    xs = [1, 2, 3]\n"
        "    assert xs\n"
        "    return 0\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_assert_int_walrus_still_fires():
    src = (
        "def f(n: int) -> int:\n"
        "    assert (x := n)\n"
        "    return x\n"
    )
    assert "X-ASSERT" in _fires(src)


def test_assert_bool_walrus_does_not_fire():
    src = (
        "def f(flag: bool) -> bool:\n"
        "    assert (x := flag)\n"
        "    return x\n"
    )
    assert "X-ASSERT" not in _fires(src)


def test_admitted_walrus_does_not_fire():
    src = "def f(n: int) -> int:\n    return (x := n)\n"
    assert "X-WALRUS" not in _fires(src)


def test_walrus_under_and_still_fires():
    src = "def f(n: int) -> bool:\n    return n > 0 and (x := n) > 0\n"
    assert "X-WALRUS" in _fires(src)


def test_walrus_in_chained_comparison_still_fires():
    src = "def f(a: int, b: int, c: int) -> bool:\n    return a < b < (x := c)\n"
    assert "X-WALRUS" in _fires(src)


def test_walrus_in_first_compare_operand_does_not_fire():
    src = "def f(a: int, b: int) -> bool:\n    return a < (x := b)\n"
    assert "X-WALRUS" not in _fires(src)


def test_walrus_in_comprehension_still_fires():
    src = "def f(l: list[int]) -> list[int]:\n    return [y := x for x in l]\n"
    assert "X-WALRUS" in _fires(src)
