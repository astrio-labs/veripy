"""Semantic and rejection checks for the Black/Django compatibility fragments."""
from pathlib import Path
import pytest
from veripy.backends.dafny.encoder import encode_module, EncodeError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.frontend.extract import parse_source
from veripy.guards.outcomes import emit_outcome_guarded
from veripy.api import verify
from veripy.backends.dafny.driver import find_dafny
from veripy.difftest.harness import difftest_file

RECORD = 'from dataclasses import dataclass\n@dataclass(frozen=True)\nclass Pair:\n    left: int\n    right: int\n'


@pytest.mark.parametrize('call', ['Pair(a, b)', 'Pair(right=b, left=a)', 'Pair(a, right=b)'])
def test_scalar_record_construction(call):
    source = RECORD + f'#@ ensures result.left == a and result.right == b\ndef f(a: int, b: int) -> Pair:\n    return {call}\n'
    text = encode_module(source, parse_source(source), 'record.py').dafny_source
    assert 'VMakePair(' in text and 'var record_arg' in text


@pytest.mark.parametrize('call', ['Pair(a)', 'Pair(a,b,0)', 'Pair(a,left=b)', 'Pair(wrong=a,right=b)', 'Pair(*[a,b])', 'Pair(True,b)'])
def test_record_constructor_rejects_invalid_bindings(call):
    source = RECORD + f'#@ ensures True\ndef f(a: int,b: int) -> Pair:\n    return {call}\n'
    with pytest.raises(EncodeError):
        encode_module(source,parse_source(source),'bad.py')


def test_record_keywords_retain_evaluation_order():
    source = RECORD + '#@ requires len(xs) > 1\n#@ ensures True\ndef f(xs: list[int]) -> Pair:\n    return Pair(right=xs[0], left=xs[1])\n'
    text = encode_module(source,parse_source(source),'order.py').dafny_source
    assert text.index(':= xs[0]') < text.index(':= xs[1]')


@pytest.mark.parametrize('typ,value', [('str','""'), ('int','0'), ('bool','False')])
def test_scalar_error_defaults_match_runtime(typ,value):
    source = f'#@ ensures raised() and result == {value}\ndef f(x: int) -> {typ}:\n    raise ValueError("test")\n'
    ns = {}; exec(emit_outcome_guarded(source,parse_source(source),'error.py',check_ensures=True),ns)
    with pytest.raises(ValueError,match='test'):
        ns['f'](1)


def test_rebound_parameter_keeps_old_input_in_contract():
    source = '#@ ensures not raised() and result == old(x) + 1\ndef f(x: int) -> int:\n    x = x + 1\n    return x\n'
    encoded = encode_outcomes(source,parse_source(source),'rebind.py').dafny_source
    assert 'var x_local := x;' in encoded
    ns = {}; exec(emit_outcome_guarded(source,parse_source(source),'rebind.py',check_ensures=True),ns)
    assert ns['f'](8) == 9


def test_rebinding_does_not_capture_existing_local():
    source = '#@ ensures not raised() and result == old(x) + 2\ndef f(x: int) -> int:\n    x_local = 1\n    x = x + x_local\n    return x + x_local\n'
    text = encode_outcomes(source,parse_source(source),'capture.py').dafny_source
    assert 'var x_local_ := x;' in text


def test_container_parameter_rebinding_stays_rejected():
    source = '#@ ensures True\ndef f(xs: list[int]) -> list[int]:\n    xs = []\n    return xs\n'
    with pytest.raises(EncodeError,match='scalar'):
        encode_outcomes(source,parse_source(source),'bad.py')


def test_mixed_tuple_assignment_is_simultaneous():
    source = '#@ ensures result == (x + 1, x)\ndef f(x: int) -> tuple[int,int]:\n    a = x\n    a, b = a + 1, a\n    return (a,b)\n'
    text = encode_module(source,parse_source(source),'tuple.py').dafny_source
    assert 'var b: int;' in text and 'a, b := (a + 1), a;' in text


@pytest.mark.parametrize('expr', ['s[0] + s', 's + s[0]', 's[0] + s[0]'])
def test_indexed_character_concatenation(expr):
    source = f'#@ requires len(s) > 0\n#@ ensures len(result) >= 2\ndef f(s: str) -> str:\n    return {expr}\n'
    text = encode_module(source,parse_source(source),'chars.py').dafny_source
    assert '[s[0]]' in text


@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
@pytest.mark.parametrize('source', [
    '#@ requires len(s) > 0\n#@ ensures len(result) == len(s) + 1\ndef f(s: str) -> str:\n    return s[0] + s\n',
    '#@ ensures result == (x + 1, x)\ndef f(x: int) -> tuple[int,int]:\n    a = x\n    a, b = a + 1, a\n    return (a,b)\n',
])
def test_new_expressions_match_compiled_python(tmp_path,source):
    path=tmp_path/'expression.py';path.write_text(source)
    result=verify(path,tmp_path/'proof',time_limit=10)
    assert result['status']=='ok',result
    comparison=difftest_file(path,tmp_path/'diff',examples=30)
    assert comparison.ok,comparison


@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_record_construction_keeps_index_obligations(tmp_path):
    source=RECORD+'#@ requires len(xs) > 0\n#@ ensures True\ndef f(xs: list[int]) -> Pair:\n    return Pair(right=xs[len(xs)], left=0)\n'
    path=tmp_path/'bad.py';path.write_text(source)
    result=verify(path,tmp_path/'proof',time_limit=10)
    assert result['status']=='failed',result
    assert any(f['kind'] in {'bounds','call-precondition'} for f in result['failures'])
