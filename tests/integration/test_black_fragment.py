"""Regression boundaries introduced by the source-preserving Black case."""
from pathlib import Path
import sys

import pytest

from veripy.backends.dafny.encoder import EncodeError, encode_module
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.frontend.extract import parse_source
from veripy.guards.emitter import GuardGenError, emit_guarded
from veripy.guards.outcomes import emit_outcome_guarded
from veripy.guards.runtime import PreconditionError, PostconditionError, TypeGuardError

CASE = Path(__file__).resolve().parents[2] / "case_studies/black"
PARSER = (CASE / "parser.py").read_text()


def encode(source):
    return encode_outcomes(source, parse_source(source)).dafny_source


def guarded(source=PARSER, post=True):
    ns = {}
    exec(emit_outcome_guarded(source, parse_source(source), "parser.py", check_ensures=post), ns)
    return ns["parse_line_ranges"]


def test_parser_emits_explicit_outcomes_without_axioms():
    text = encode(PARSER)
    assert "returns (result: seq<(int, int)>," in text
    assert "opaque function PyTryDecimal" in text
    assert "break conversion_try" in text
    assert "{:axiom}" not in text


@pytest.mark.parametrize("edit", [
    lambda s: s.replace("except ValueError:", "except Exception:"),
    lambda s: s.replace("except ValueError:", "except ValueError as exc:"),
    lambda s: s.replace("start = int(parts[0])", "start = int(parts[0], 10)"),
    lambda s: s.replace("start = int(parts[0])", "start = len(parts[0])"),
    lambda s: s.replace("from None", "from ValueError('nested')"),
    lambda s: s.replace("f\" {lines_str!r}\"", "f\" {len(lines_str)}\""),
    lambda s: s.replace("def parse_line_ranges", "@other\ndef parse_line_ranges"),
    lambda s: "from typing import Optional as ValueError\n" + s,
    lambda s: "from typing import Optional as int\n" + s,
    lambda s: "x = unknown()\n" + s,
    lambda s: s.replace("    lines: list", "    ValueError = 1\n    lines: list"),
    lambda s: s.replace("    lines: list", "    raised = 1\n    lines: list"),
    lambda s: s.replace("    return lines", "    pass"),
    lambda s: s.replace("    return lines", "    return"),
])
def test_outcome_backend_rejects_unmodeled_execution(edit):
    with pytest.raises(EncodeError):
        encode(edit(PARSER))


@pytest.mark.parametrize("values", [[], ["1-2"], ["２-٣", "0-0", "2-1"], ["1_0-2_0"], [" +1 - +2 "]])
def test_guard_preserves_results(values):
    ns = {}
    exec(PARSER, ns)
    assert guarded()(values) == ns["parse_line_ranges"](values)


@pytest.mark.parametrize("values", [["x"], ["1-x"], ["1-2", "-1-2"], ["\x1c1-2"]])
def test_guard_preserves_error_message_and_cause(values):
    ns = {}
    exec(PARSER, ns)
    with pytest.raises(ValueError) as original:
        ns["parse_line_ranges"](values)
    with pytest.raises(ValueError) as wrapped:
        guarded()(values)
    assert str(wrapped.value) == str(original.value)
    assert wrapped.value.__suppress_context__ == original.value.__suppress_context__
    assert wrapped.value.__cause__ is original.value.__cause__ is None


@pytest.mark.parametrize("bad", [("1-2",), [True], ["\ud800-2"], "1-2"])
def test_guard_rejects_outside_boundary(bad):
    with pytest.raises(TypeGuardError):
        guarded()(bad)


def test_guard_rejects_changed_digit_limit():
    fn = guarded()
    previous = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(640 if previous != 640 else 0)
        with pytest.raises(PreconditionError, match="configuration changed"):
            fn(["1-2"])
    finally:
        sys.set_int_max_str_digits(previous)


def test_error_postcondition_is_actually_checked():
    source = PARSER.replace("#@ ensures raised() ==", "#@ ensures not raised() and raised() ==")
    with pytest.raises(PostconditionError):
        guarded(source)(["1-x"])


def test_normal_guard_cannot_silently_ignore_outcome_contracts():
    with pytest.raises(GuardGenError, match="emit_outcome_guarded"):
        emit_guarded(PARSER, parse_source(PARSER), "parser.py")


def test_count_full_substring_signature_only():
    source = '#@ ensures result >= 0\ndef count(s: str, sub: str) -> int:\n    return s.count(sub)\n'
    assert "PyStrCount(s, sub)" in encode_module(source, parse_source(source), "test.py").dafny_source
    for expr in ("s.count(sub, 1)", "s.count(sub=sub)", "s.count(1)"):
        bad = source.replace("s.count(sub)", expr)
        with pytest.raises(EncodeError):
            encode_module(bad, parse_source(bad), "test.py")


def test_rebinding_element_target_uses_independent_cursor():
    source = '#@ ensures result >= 0\ndef f(xs: list[int]) -> int:\n    n = 0\n    for x in xs:\n        #@ invariant n == loop_index()\n        x = 0\n        n += 1\n    return n\n'
    text = encode_module(source, parse_source(source), "test.py").dafny_source
    assert "x := 0" in text
    assert "invariant (n == x_i" in text


@pytest.mark.parametrize("source", [
    '#@ ensures loop_index() == 0\ndef f() -> int:\n    return 0\n',
    '#@ ensures result == 0\ndef f(loop_index: int, xs: list[int]) -> int:\n    for x in xs:\n        #@ invariant loop_index() >= 0\n        pass\n    return 0\n',
    '#@ ensures result == 0\ndef f() -> int:\n    return loop_index()\n',
    '#@ ensures result == 0\ndef f(xs: list[int]) -> int:\n    for i, x in enumerate(xs):\n        i = 1\n    return 0\n',
    '#@ ensures result == 0\ndef f(xs: list[int]) -> int:\n    for x in xs:\n        x = 0\n    return x\n',
])
def test_loop_cursor_and_target_scope_rejections(source):
    with pytest.raises(EncodeError):
        encode_module(source, parse_source(source), "test.py")
