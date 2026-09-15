"""Deterministic global initialization, checked use and runtime stability."""
import ast
from pathlib import Path
import pytest
from veripy.api import verify
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.encoder import encode_module,EncodeError
from veripy.backends.dafny.environment import resolve_module,EnvironmentError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.backends.dafny.driver import find_dafny
from veripy.guards.emitter import emit_guarded
from veripy.guards.outcomes import emit_outcome_guarded
from veripy.guards.runtime import PreconditionError

SOURCE='''TABLE = [1]
for item in [2, 3]:
    TABLE.append(TABLE[-1] + item)
del item
#@ ensures result == 10
def total(x: int) -> int:
    return TABLE[0] + TABLE[1] + TABLE[2]
'''


def test_constant_initialization_preserves_python_semantics():
    e=resolve_module(ast.parse(SOURCE));ns={};exec(SOURCE,ns)
    assert e.values=={'TABLE':[1,3,6]}
    assert e.values['TABLE']==ns['TABLE']
    text=encode_module(SOURCE,parse_source(SOURCE),'c.py').dafny_source
    assert '[1, 3, 6]' in text


@pytest.mark.parametrize('backend',['dafny','dafny-outcomes'])
@pytest.mark.skipif(not find_dafny(),reason='Dafny required')
def test_constants_verify_and_guards_reject_mutation(tmp_path,backend):
    source=SOURCE if backend=='dafny' else SOURCE.replace('#@ ensures result == 10','#@ ensures not raised() and result == 10')
    path=tmp_path/'c.py';path.write_text(source)
    report=verify(path,tmp_path/'out',backend=backend)
    assert report['status']=='ok',report
    emit=emit_guarded if backend=='dafny' else emit_outcome_guarded
    ns={};exec(emit(source,parse_source(source),'c.py',check_ensures=True),ns)
    assert ns['total'](0)==10
    ns['TABLE'][0]=99
    with pytest.raises(PreconditionError,match='module environment changed'):ns['total'](0)


def test_initialized_helpers_use_real_body_not_contract():
    source='''#@ ensures True
def days(y: int) -> int:
    z = y - 1
    return z * 365 + z // 4 - z // 100 + z // 400
CYCLE = days(401)
#@ ensures result == 146097
def f(x: int) -> int:
    return CYCLE
'''
    assert resolve_module(ast.parse(source)).values['CYCLE']==146097
    assert '146097' in encode_module(source,parse_source(source),'c.py').dafny_source


@pytest.mark.parametrize('initializer',[
    'A = open("/tmp/untrusted")',
    'A = [1]\nA.append(A)',
    'A = 1\nassert A == 2',
    'A = [0] * 1000000000',
    'A = 1 // 0',
    'A = 1\nimport math as A',
    'import math\nmath = 1',
    'A = 1\nclass A:\n    pass',
])
def test_initializer_fails_closed(initializer):
    with pytest.raises(EnvironmentError):resolve_module(ast.parse(initializer))


def test_global_mutation_and_alias_append_rejected():
    for body in ['    TABLE.append(9)\n    return 0','    alias = TABLE\n    alias.append(9)\n    return 0','    global TABLE\n    TABLE = [9]\n    return 0']:
        source='TABLE = [1]\n#@ ensures True\ndef f(x: int) -> int:\n'+body+'\n'
        with pytest.raises(EncodeError):encode_module(source,parse_source(source),'c.py')


def test_local_shadowing_is_not_replaced_by_module_data():
    source='X = 99\n#@ ensures result == X\ndef f(X: int) -> int:\n    return X\n'
    text=encode_module(source,parse_source(source),'c.py').dafny_source
    assert 'result := X' in text


def test_outcome_guard_specs_resolve_real_module_globals():
    source='C = 7\n#@ ensures not raised() and result == C\ndef f(x: int) -> int:\n    return C\n'
    ns={};exec(emit_outcome_guarded(source,parse_source(source),'c.py',check_ensures=True),ns)
    assert ns['f'](0)==7
    ns['C']=8
    with pytest.raises(PreconditionError):ns['f'](0)


def test_initializer_observes_list_growth():
    source = "A = [1]\nfor x in A:\n    if x < 3:\n        A.append(x + 1)\ndel x\n"
    ns = {}; exec(source, ns)
    assert resolve_module(ast.parse(source)).values['A'] == ns['A'] == [1, 2, 3]


def test_initializer_helper_local_read_before_assignment_fails():
    source = "X = 7\ndef f():\n    y = X\n    X = 2\n    return y\nC = f()\n"
    with pytest.raises(EnvironmentError, match='unresolved'):
        resolve_module(ast.parse(source))


def test_dependency_inventory_is_explicit_even_without_constants():
    source = "from math import gcd as common\nimport re\nfrom stdnum.exceptions import *\n"
    dependencies = resolve_module(ast.parse(source)).dependencies
    assert [d['resolution'] for d in dependencies] == ['encoder-model', 'encoder-model', 'encoder-model']
    assert dependencies[0]['binding'] == 'common'
    assert all(not d['executed_by_resolver'] for d in dependencies)


def test_initializer_augmented_list_assignment_preserves_aliases():
    source = "A = [1]\nB = A\nA += [2]\n"
    assert resolve_module(ast.parse(source)).values == {'A': [1, 2], 'B': [1, 2]}


def test_initializer_does_not_call_shadowed_builtin():
    source = "def f(len):\n    return len([1])\nA = f(7)\n"
    with pytest.raises(EnvironmentError, match='shadowed'):
        resolve_module(ast.parse(source))


def test_initializer_augmented_repetition_preserves_aliases():
    assert resolve_module(ast.parse("A=[1]\nB=A\nA*=2\n")).values == {'A':[1,1],'B':[1,1]}


@pytest.mark.parametrize('definition', [
    'def unused(x=touch()):\n    return 0',
    'def unused(x: touch()):\n    return 0',
    'class Unused:\n    C = touch()',
])
def test_definition_time_effects_do_not_create_false_constants(definition):
    source='C = 1\n'+definition+'\n#@ ensures result == 1\ndef f(x: int) -> int:\n    return C\n'
    with pytest.raises(EncodeError):encode_module(source,parse_source(source),'bad.py')


def test_untrusted_generic_annotation_cannot_run_during_constant_initialization():
    source="from external import List\nX = 1\ndef f(x: List[int]):\n    return X\n"
    with pytest.raises(EnvironmentError,match='explicit typing import'):
        resolve_module(ast.parse(source))
