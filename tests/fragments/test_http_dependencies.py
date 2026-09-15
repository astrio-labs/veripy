"""The HTTP dependency is explicit and rejects identity/eager-domain shortcuts."""
import pytest
from veripy.backends.dafny.encoder import EncodeError, encode_module
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.http_strings import PATTERN

PREFIX='import re\nfrom werkzeug import datastructures as ds\nR = re.compile('+repr(PATTERN)+')\n'

@pytest.mark.parametrize('extra', ['from unknown import thing as ds\n', 'ds = 1\n', 'def ds():\n    return 1\n'])
def test_http_dependency_rebinding_rejected(extra):
    source=PREFIX+extra+'#@ ensures True\ndef f(s: str) -> bool:\n    return R.match(s,0) is not None\n'
    with pytest.raises(EncodeError,match='dependency'):
        encode_module(source,parse_source(source),'http.py')


def test_regex_capture_identity_not_structural():
    source=PREFIX+'#@ ensures True\ndef f(s: str) -> bool:\n    return R.match(s,0) == R.match(s,0)\n'
    with pytest.raises(EncodeError,match='presence checks'):
        encode_module(source,parse_source(source),'http.py')


def test_optional_string_truth_checks_presence_and_empty():
    source='#@ ensures True\ndef f(s: str | None) -> bool:\n    return bool(s)\n'
    text=encode_module(source,parse_source(source),'optional.py').dafny_source
    assert '.PySome?' in text and ').v| != 0' in text


@pytest.mark.parametrize('expression', [
    '(R.match(s,0),1) == (R.match(s,0),1)',
    '[R.match(s,0)] == [R.match(s,0)]',
    'R.match(s,0) in [R.match(s,0)]',
    'ds.ETags() == ds.ETags()',
])
def test_nested_dependency_identity_does_not_become_value_equality(expression):
    source=PREFIX+'#@ ensures True\ndef f(s: str) -> bool:\n    return '+expression+'\n'
    with pytest.raises(EncodeError,match='presence checks'):
        encode_module(source,parse_source(source),'http.py')


def test_etags_constructor_rejects_metaclass_call_override():
    from abc import ABCMeta
    from types import SimpleNamespace
    from veripy.backends.dafny.http_strings import _constructor_model, guard_dependency
    from veripy.guards.runtime import PreconditionError
    class Honest(metaclass=ABCMeta):
        __init__ = _constructor_model
    class Replacing(ABCMeta):
        def __call__(cls,*args,**kwargs):return None
    class Dishonest(metaclass=Replacing):
        __init__ = _constructor_model
    namespace={'ds':SimpleNamespace(ETags=Honest)}
    exec('def function(): pass',namespace)
    guard_dependency(namespace['function'])
    namespace['ds'].ETags=Dishonest
    with pytest.raises(PreconditionError,match='constructor dependency'):
        guard_dependency(namespace['function'])
