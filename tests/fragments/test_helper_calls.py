"""Checked scalar composition: modular proofs and translation boundaries."""
import ast
import subprocess
from pathlib import Path

import pytest

from veripy.api import verify
from veripy.backends.dafny.driver import find_dafny
from veripy.backends.dafny.encoder import EncodeError, encode_module
from veripy.difftest.harness import (
    _compiled_member, _load_compiled_module, _load_original_module,
    difftest_file, from_dafny, to_dafny,
)
from veripy.frontend.extract import parse_source


STEP = '''#@ requires x >= 0
#@ ensures result == x + 1
def step(x: int) -> int:
    return x + 1

'''
CALLER = '''#@ requires x >= 0
#@ ensures result == x + 2
def caller(x: int) -> int:
    return step(step(x))
'''


def encode(source):
    return encode_module(source, parse_source(source), "calls.py")


def caller(expression, returns="int"):
    return f"#@ ensures True\ndef caller(x: int) -> {returns}:\n    return {expression}\n"


@pytest.mark.parametrize("source, message", [
    (STEP.replace("#@ ensures result == x + 1\n", "") + CALLER, "postcondition"),
    (STEP.replace("return x + 1", "return step(x)") + CALLER, "recursive"),
    (STEP.replace("return x + 1", "return caller(x)") + CALLER, "recursive"),
    (STEP + CALLER + "step = caller\n", "initialization/rebinding"),
    (STEP + CALLER.replace("def caller(x:", "def caller(step: int, x:"), "shadows a helper"),
    (STEP + CALLER.replace("    return", "    step = 2\n    return"), "shadows a helper"),
    (STEP.replace("def step", "@decorate\ndef step") + CALLER, "decorated"),
    ("from math import gcd as step\n" + STEP + CALLER, "shadows a helper"),
    ("from .typing import Optional\n" + STEP + CALLER, "initialization/rebinding"),
    (STEP + CALLER + "def extra(x=side_effect()):\n    return x\n", "explicitly specified"),
    (STEP + CALLER.replace("    return", "    global step\n    return"), "global/nonlocal"),
    (STEP + CALLER.replace("return step(step(x))", "return missing(x)"), "outside"),
    (STEP.replace("x: int", "x: list[int]") + CALLER, "non-int operands"),
    (STEP.replace("-> int", "-> list[int]") + CALLER, "helper argument type"),
    (STEP.replace("x: int", "x: int = int(1)") + CALLER, "defaults"),
    (STEP + caller("step()"), "missing helper"),
    (STEP + caller("step(x, x)"), "positional"),
    (STEP + caller("step(x, x=x)"), "keyword"),
    (STEP + caller("step(y=x)"), "keyword"),
    (STEP + caller("step(**{})"), "keyword"),
    (STEP + caller("step(*[x])"), "positional"),
    (STEP + caller("step(True)"), "type"),
    (STEP + caller('step("x")'), "type"),
    (STEP + caller("step(None)"), "type"),
    (STEP + caller("step(x) if x > 0 else 0"), "eager scalar"),
    (STEP + caller("step(x) or 1"), "must be boolean"),
    (STEP + caller("max(step(x), 0)"), "eager scalar"),
    (STEP + caller("step((a := x))"), "walrus"),
    (STEP + caller("[step(x)]", "list[int]"), "eager scalar"),
    (STEP + CALLER.replace("#@ ensures result == x + 2", "#@ ensures result == step(x)"), "spec expressions"),
    (STEP + CALLER.replace("    return step(step(x))", "    while step(x) > 0:\n        pass\n    return x"), "loop headers"),
    (STEP + CALLER.replace("    return step(step(x))", "    for i in range(step(x)):\n        pass\n    return x"), "loop headers"),
])
def test_unsupported_composition_fails_closed(source, message):
    with pytest.raises(EncodeError, match=message):
        encode(source)


def test_call_binding_positional_only_and_keyword_only():
    helper = '''#@ ensures result == x - y
def subtract(x: int, /, *, y: int) -> int:
    return x - y
'''
    encode(helper + caller("subtract(x, y=2)"))
    for expr in ["subtract(x=x, y=2)", "subtract(x, 2)"]:
        with pytest.raises(EncodeError):
            encode(helper + caller(expr))


def test_partial_left_operand_is_evaluated_before_later_helper():
    e = encode(STEP + caller("(10 // x) + step(x)"))
    body = e.dafny_source.split("method caller", 1)[1]
    assert body.index("PyFloorDiv(10, x)") < body.index(":= step(")
    call_line = next(i for i, s in enumerate(e.dafny_source.splitlines(), 1) if ":= step(" in s)
    assert e.line_map[call_line] == 8


requires_dafny = pytest.mark.skipif(find_dafny() is None, reason="Dafny required")


@requires_dafny
def test_nested_calls_verify_and_execute(tmp_path: Path):
    path = tmp_path / "nested.py"
    path.write_text(STEP + CALLER)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "ok", result
    diff = difftest_file(path, tmp_path / "diff", examples=40)
    assert diff.ok, diff


@requires_dafny
@pytest.mark.parametrize("source, kind, function", [
    (STEP + CALLER.replace("#@ requires x >= 0\n", ""), "call-precondition", "caller"),
    (STEP.replace("return x + 1", "return x + 2") + CALLER, "postcondition", "step"),
])
def test_bad_caller_or_callee_invalidates_module(tmp_path, source, kind, function):
    path = tmp_path / "bad.py"
    path.write_text(source)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "failed", result
    call_or_return = next(n for n in ast.walk(ast.parse(source))
                          if isinstance(n, ast.FunctionDef) and n.name == function).body[0].lineno
    assert any(f["kind"] == kind and f["py_line"] == call_or_return
               for f in result["failures"]), result


SCALARS = '''#@ ensures result == x
def optional(x: int | None) -> int | None:
    return x

#@ ensures result == x
def relay(x: int | None) -> int | None:
    return optional(x)

#@ ensures result is None
def nothing(x: int) -> int | None:
    return optional(None)

#@ ensures result == x
def inject(x: int) -> int | None:
    return optional(x)

#@ ensures result == x
def text(x: str) -> str:
    return x

#@ ensures result == x + "!"
def greet(x: str) -> str:
    return text(x) + "!"

#@ ensures result == x
def boolean(x: bool) -> bool:
    return x

#@ ensures result == (not x)
def invert(x: bool) -> bool:
    return not boolean(x)

#@ ensures result == x
def optional_flag(x: bool | None) -> bool | None:
    return x

#@ ensures result == x
def relay_flag(x: bool | None) -> bool | None:
    return optional_flag(x)

#@ ensures result == x
def optional_text(x: str | None) -> str | None:
    return x

#@ ensures result == x
def relay_text(x: str | None) -> str | None:
    return optional_text(x)
'''


@requires_dafny
def test_scalar_and_optional_calls_verify_and_execute(tmp_path):
    path = tmp_path / "scalars.py"
    path.write_text(SCALARS)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "ok", result
    diff = difftest_file(path, tmp_path / "diff", examples=25)
    assert diff.ok, diff


@requires_dafny
def test_private_callee_keyword_reordering_and_collision(tmp_path):
    source = '''#@ ensures result == x - y
def _subtract(x: int, y: int) -> int:
    return x - y

#@ ensures result == x - 2
def caller(x: int) -> int:
    py_subtract = 2
    return _subtract(y=py_subtract, x=x)
'''
    path = tmp_path / "private.py"
    path.write_text(source)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "ok", result
    diff = difftest_file(path, tmp_path / "diff", examples=30)
    assert diff.ok, diff


def compile_source(source, tmp_path):
    path = tmp_path / "execution.py"
    path.write_text(source)
    encoded = encode(source)
    stub = tmp_path / "execution.dfy"
    stub.write_text(encoded.dafny_source)
    proc = subprocess.run([find_dafny(), "translate", "py", str(stub),
                           "--output", str(tmp_path / "compiled"), "--no-verify",
                           "--allow-warnings"], capture_output=True, text=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    return _load_original_module(path), _load_compiled_module(tmp_path / "compiled-py"), encoded


@requires_dafny
def test_keyword_values_execute_in_written_order(tmp_path, monkeypatch):
    source = '''#@ ensures result == x
def mark(x: int) -> int:
    return x

#@ ensures result == 10 * x + y
def combine(x: int, y: int) -> int:
    return 10 * x + y

#@ ensures result == 12
def caller() -> int:
    return combine(y=mark(2), x=mark(1))
'''
    original, compiled, encoded = compile_source(source, tmp_path)
    events = []

    def mark(x):
        events.append(x)
        return x

    monkeypatch.setattr(original, "mark", mark)
    assert original.caller() == 12
    assert events == [2, 1]
    events.clear()
    monkeypatch.setattr(compiled.default__, "mark", staticmethod(mark))
    assert _compiled_member(compiled.default__, encoded.method_names["caller"])() == 12
    assert events == [2, 1]


@requires_dafny
def test_earlier_division_error_precedes_later_helper_at_runtime(tmp_path, monkeypatch):
    original, compiled, encoded = compile_source(STEP + caller("(10 // x) + step(x)"), tmp_path)
    events = []

    def step(x):
        events.append(x)
        return x + 1

    monkeypatch.setattr(original, "step", step)
    monkeypatch.setattr(compiled.default__, "step", staticmethod(step))
    for fn in [original.caller, _compiled_member(compiled.default__, encoded.method_names["caller"])]:
        with pytest.raises(ZeroDivisionError):
            fn(0)
        assert events == []


@requires_dafny
def test_optional_values_include_none_zero_and_negative(tmp_path):
    original, compiled, encoded = compile_source(SCALARS, tmp_path)
    relay = _compiled_member(compiled.default__, encoded.method_names["relay"])
    opt = (relay.__globals__["PyOpt_PyNone"], relay.__globals__["PyOpt_PySome"])
    for x in [None, 0, -1, 1, -(10 ** 50), 10 ** 50]:
        assert from_dafny(relay(to_dafny(x, ("opt", "int"), opt=opt)), ("opt", "int")) == original.relay(x)
    for name, dtype, values in [("relay_flag", "bool", [None, False, True]),
                                ("relay_text", "str", [None, "", "é🙂", "\0\n"])]:
        fn = _compiled_member(compiled.default__, encoded.method_names[name])
        for x in values:
            assert from_dafny(fn(to_dafny(x, ("opt", dtype), opt=opt)), ("opt", dtype)) == getattr(original, name)(x)


@requires_dafny
def test_calls_remain_inside_branches_and_loop_bodies(tmp_path):
    source = STEP + '''#@ ensures result == (x + 1 if x >= 0 else x)
def branch(x: int) -> int:
    if x >= 0:
        return step(x)
    return x

#@ requires x >= 0
#@ ensures result == x + 3
def repeat(x: int) -> int:
    value = x
    for i in range(3):
        #@ invariant value == x + i
        value = step(value)
    return value
'''
    path = tmp_path / "branch_loop.py"
    path.write_text(source)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "ok", result
    diff = difftest_file(path, tmp_path / "diff", examples=30)
    assert diff.ok, diff
