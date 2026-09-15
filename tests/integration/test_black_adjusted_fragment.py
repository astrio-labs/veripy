"""General fragment regressions exposed by Black's range mapping consumer."""
from pathlib import Path
import pytest
from veripy.backends.dafny.encoder import encode_module, EncodeError
from veripy.frontend.extract import parse_source
from veripy.guards.emitter import emit_guarded, GuardGenError


def encode(source): return encode_module(source,parse_source(source),'test.py').dafny_source

@pytest.mark.parametrize('arity',[2,3])
def test_sorted_preserves_tuple_type_in_body_and_spec(arity):
    t='tuple['+', '.join(['int']*arity)+']'
    source=f'#@ ensures result == sorted(xs)\ndef f(xs: list[{t}]) -> list[{t}]:\n    return sorted(xs)\n'
    text=encode(source)
    assert text.count(f'PySorted{arity}(xs)')==2
    ns={}; exec(emit_guarded(source,parse_source(source),'test.py',check_ensures=True),ns)
    values=[tuple([0]*arity),tuple([-1]*arity),tuple([0]*arity)]
    assert ns['f'](values)==sorted(values)
    assert values[0]==tuple([0]*arity)

@pytest.mark.parametrize('annotation',['tuple[int, str]','tuple[int, int, int, int]','bool','str'])
def test_sorted_other_domains_rejected(annotation):
    source=f'#@ ensures True\ndef f(xs: list[{annotation}]) -> list[{annotation}]:\n    return sorted(xs)\n'
    with pytest.raises(EncodeError): encode(source)

@pytest.mark.parametrize('expr',['sorted(xs, reverse=True)','sorted(xs, key=abs)','sorted(xs, xs)'])
def test_sorted_options_remain_rejected(expr):
    source=f'#@ ensures True\ndef f(xs: list[tuple[int, int]]) -> list[tuple[int, int]]:\n    return {expr}\n'
    with pytest.raises(EncodeError): encode(source)


def test_tuple_truth_retains_operand_bounds_obligation():
    source='#@ requires 0 <= i < len(xs)\n#@ ensures result == False\ndef f(xs: list[tuple[int, int]], i: int) -> bool:\n    return not xs[i]\n'
    text=encode(source)
    assert 'PyIndex(i, |xs|)' in text and '; false)' in text
    cond=source.replace('return not xs[i]','if xs[i]:\n        return False\n    return True')
    assert '; true)' in encode(cond)


def test_private_frozen_record_guard_and_encoder():
    source='from dataclasses import dataclass\n@dataclass(frozen=True)\nclass _Range:\n    lo: int\n#@ ensures result == item.lo\ndef f(item: _Range) -> int:\n    return item.lo\n'
    assert 'VRec_Range' in encode(source)
    ns={}; exec(emit_guarded(source,parse_source(source),'test.py',check_ensures=True),ns)
    assert ns['f'](ns['_Range'](-2))==-2
    with pytest.raises(EncodeError): encode(source.replace('_Range','__Range'))
    with pytest.raises(EncodeError): encode(source.replace('frozen=True','frozen=False'))


def test_actual_black_predicate_retains_negative_ranges():
    path=Path(__file__).resolve().parents[2]/'case_studies/black/adjusted.py'
    source=path.read_text(); ns={}
    exec(emit_guarded(source,parse_source(source),'consumer.py',check_ensures=True),ns)
    assert ns['is_valid_line_range']((-5,-1)) is True
    assert ns['is_valid_line_range']((2,1)) is False


@pytest.mark.parametrize('name', ['_veripy_hidden', '_VeripyPostconditionError', '_VERIPY_ISLAND_SHA256'])
def test_private_records_cannot_capture_generated_guard_bindings(name):
    source=f'from dataclasses import dataclass\n@dataclass(frozen=True)\nclass {name}:\n    lo: int\n#@ ensures result == item.lo\ndef f(item: {name}) -> int:\n    return item.lo\n'
    with pytest.raises(GuardGenError, match='reserved'):
        emit_guarded(source,parse_source(source),'test.py',check_ensures=True)


def test_nonreserved_capitalized_private_function_remains_accepted():
    source='#@ ensures result == x\ndef _VeripyApplicationFunction(x: int) -> int:\n    return x\n'
    ns={}
    exec(emit_guarded(source,parse_source(source),'test.py',check_ensures=True),ns)
    assert ns['_VeripyApplicationFunction'](-3)==-3
