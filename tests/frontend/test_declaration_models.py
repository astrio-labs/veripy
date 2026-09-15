"""Explicit scalar identities, default binding, and named exception models."""
import pytest
from veripy.backends.dafny.encoder import encode_module,EncodeError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.frontend.extract import parse_source
from veripy.guards.outcomes import emit_outcome_guarded
from veripy.guards.emitter import emit_guarded
from veripy.guards.runtime import PreconditionError

SOURCE='''from typing import NewType, cast
Name = NewType("Name", str)
class InvalidName(ValueError):
    pass
#@ ensures raised() == reject
#@ ensures not raised() ==> result == value
def f(value: str, *, reject: bool = False) -> Name:
    if reject:
        raise InvalidName("invalid")
    return cast("Name", value)
'''


def test_named_error_and_newtype_keep_native_identity():
    text=encode_outcomes(SOURCE,parse_source(SOURCE),'name.py').dafny_source
    assert 'returns (result: string,' in text
    ns={};exec(emit_outcome_guarded(SOURCE,parse_source(SOURCE),'name.py',check_ensures=True),ns)
    assert ns['f']('abc')=='abc'
    with pytest.raises(ns['InvalidName']):ns['f']('abc',reject=True)
    ns['cast']=lambda _,value: 'corrupted'
    with pytest.raises(PreconditionError,match='cast dependency'):ns['f']('abc')


@pytest.mark.parametrize('change',[
    ('pass','def __init__(self, value):\n        print(value)'),
    ('Name = NewType("Name", str)','Name = NewType("Wrong", str)'),
    ('#@ ensures raised()', 'cast = lambda t, v: 0\n#@ ensures raised()'),
])
def test_unmodeled_declarations_rejected(change):
    s=SOURCE.replace(*change)
    with pytest.raises(EncodeError):encode_outcomes(s,parse_source(s),'bad.py')


def test_helper_default_is_bound_and_guarded():
    source='''#@ ensures result == x + 1
def step(x: int = 3) -> int:
    return x + 1
#@ ensures result == 4
def f() -> int:
    return step()
'''
    text=encode_module(source,parse_source(source),'defaults.py').dafny_source
    assert ':= 3;' in text
    ns={};exec(emit_guarded(source,parse_source(source),'defaults.py',check_ensures=True),ns)
    assert ns['step']()==4 and ns['f']()==4


@pytest.mark.parametrize('signature',['x: int = None','x: int = True','x: list[int] = []','x: str = str(1)'])
def test_unsafe_or_mistyped_defaults_fail(signature):
    source='#@ ensures True\ndef f('+signature+') -> int:\n    return 0\n'
    with pytest.raises(EncodeError):encode_module(source,parse_source(source),'bad.py')
