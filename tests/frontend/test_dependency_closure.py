import ast
import json
import subprocess
import sys
from pathlib import Path
import pytest
from veripy.frontend.closure import extract_candidate


def test_transitive_source_preservation_and_annotations():
    source='''SHIFT = 3
#@ ensures result == x + 3
def helper(x: int) -> int:
    return x + SHIFT

def unused(x):
    return missing(x)

#@ ensures result == x + 3
def target(x: int) -> int:
    return helper(x)
'''
    result=extract_candidate(source,'target')
    assert result['status']=='extracted'
    assert set(result['nodes'])=={'SHIFT','helper','target','int'}
    candidate=result['candidate_source']
    assert '#@ ensures result == x + 3' in candidate and 'def unused' not in candidate
    original={n.name:ast.dump(n,include_attributes=True) for n in ast.parse(source).body if isinstance(n,ast.FunctionDef)}
    assert all(ast.dump(n,include_attributes=True)==original[n.name] for n in ast.parse(candidate).body if isinstance(n,ast.FunctionDef))

@pytest.mark.parametrize('expression',[
    '[offset + x for x in values]',
    '{x: offset + x for x in values}',
    'tuple(offset + x for x in values)',
])
def test_comprehensions_do_not_invent_globals(expression):
    source=f'offset=3\nvalues=[1,2]\nTABLE={expression}\ndef f():\n    return TABLE\n'
    result=extract_candidate(source,'f')
    assert result['status']=='extracted'
    assert 'x' not in result['nodes'] and {'offset','values'}<=set(result['nodes'])


def test_nested_generator_captures_external_dependency():
    result=extract_candidate('def f(xs):\n    return sum(missing(x) for x in xs)\n','f')
    assert result['status']=='blocked' and result['candidate_source'] is None
    assert {'kind':'unresolved','name':'missing'} in result['issues']

@pytest.mark.parametrize('source,kind',[
 ('TABLE=[1]\nTABLE=[2]\ndef f():\n    return TABLE\n','ambiguous-binding'),
 ('TABLE=[1]\nTABLE[0]=2\ndef f():\n    return TABLE\n','module-mutation'),
 ('TABLE=[1]\nTABLE.append(2)\ndef f():\n    return TABLE\n','module-call-on-dependency'),
 ('if flag:\n    TABLE=[1]\ndef f():\n    return TABLE\n','dynamic-binding'),
 ('from unknown import *\ndef f():\n    return 1\n','wildcard-import'),
 ('TABLE=1\ndef f():\n    global TABLE\n    TABLE=2\n    return TABLE\n','nonlocal-state'),
 ('def f():\n    return __name__\n','unresolved'),
])
def test_unsafe_or_ambiguous_boundaries_fail_closed(source,kind):
    result=extract_candidate(source,'f')
    assert result['candidate_source'] is None and any(i['kind']==kind for i in result['issues'])


def test_imports_defaults_forward_types_and_builtin_shadowing_preserved():
    source='''from __future__ import annotations
from external import Thing
DEFAULT = 3
def len(x):
    return 9
def f(x: "Thing", y=DEFAULT):
    return len(x)
'''
    result=extract_candidate(source,'f')
    assert result['status']=='extracted'
    assert result['nodes']['len']['kind']=='local-function'
    assert result['nodes']['Thing']['import']['resolution']=='unresolved'
    assert 'from __future__ import annotations' in result['candidate_source']
    assert result['verification_status']=='not-run'


def test_extraction_never_executes_initializer(tmp_path):
    sentinel=tmp_path/'executed'
    source=f'VALUE = open({str(sentinel)!r}, "w")\ndef f():\n    return VALUE\n'
    result=extract_candidate(source,'f')
    assert not sentinel.exists()
    assert result['nodes']['open']=={'kind':'builtin','modeled_surface':False}


def test_cli_preserves_existing_outputs(tmp_path):
    source=tmp_path/'source.py';source.write_text('def f(x: int) -> int:\n    return x\n')
    out=tmp_path/'out'
    command=[sys.executable,'-m','veripy.frontend.closure',str(source),'--function','f','--out',str(out)]
    first=subprocess.run(command,capture_output=True,text=True);assert first.returncode==0,first.stderr
    assert json.loads((out/'dependencies.json').read_text())['verification_status']=='not-run'
    snapshot=(out/'candidate.py').read_bytes()
    assert subprocess.run(command,capture_output=True).returncode!=0
    assert (out/'candidate.py').read_bytes()==snapshot


def test_extracted_annotated_helper_and_constant_verify(tmp_path):
    from veripy.api import verify
    from veripy.backends.dafny.driver import find_dafny
    if find_dafny() is None:pytest.skip('Dafny unavailable')
    source='''SHIFT = 3
#@ ensures result == x + 3
def helper(x: int) -> int:
    return x + SHIFT

def unrelated(x):
    return unknown(x)

#@ ensures result == x + 3
def target(x: int) -> int:
    return helper(x)
'''
    result=extract_candidate(source,'target');assert result['status']=='extracted'
    candidate=tmp_path/'candidate.py';candidate.write_text(result['candidate_source'])
    proof=verify(candidate,tmp_path/'proof',backend='dafny',time_limit=30,keep_artifacts=True)
    assert proof['status']=='ok',proof


def test_import_inside_function_is_reported():
    source='def f(x):\n    from external import transform\n    return transform(x)\n'
    result=extract_candidate(source,'f')
    assert result['status']=='extracted'
    assert result['imports'][0]['module']=='external'
    assert result['imports'][0]['resolution']=='unresolved'
    assert 'from external import transform' in result['candidate_source']

@pytest.mark.parametrize('import_line,decorator', [
    ('import typing as t', 't.overload'),
    ('from typing import overload as ov', 'ov'),
    ('from typing_extensions import overload', 'overload'),
])
def test_overload_group_retains_signatures_and_implementation(import_line, decorator):
    source=f'''{import_line}
@{decorator}
def f(x: int) -> int: ...
@{decorator}
def f(x: str) -> str: ...
def f(x: int | str) -> int | str:
    return x
'''
    result=extract_candidate(source,'f')
    assert result['status']=='extracted',result
    assert result['candidate_source']==source
    assert result['nodes']['f']['line']==6
    assert result['nodes']['f']['overload_lines']==[3,5]
    assert result['verification_status']=='not-run'

@pytest.mark.parametrize('source', [
    'def overload(f): return f\n@overload\ndef f(x): ...\ndef f(x): return x\n',
    'import typing as t\nt = other\n@t.overload\ndef f(x): ...\ndef f(x): return x\n',
    'import typing as t\n@t.overload\ndef f(x): return changed(x)\ndef f(x): return x\n',
    'import typing as t\n@t.overload\ndef f(x): ...\n@wrapper\ndef f(x): return x\n',
    'import typing as t\ndef f(x): return x\n@t.overload\ndef f(x): ...\n',
    'from .typing import overload\n@overload\ndef f(x): ...\ndef f(x): return x\n',
    'import typing as t\n@t.overload\ndef f(x): ...\ndef f(x): return x\nf = wrapper(f)\n',
])
def test_runtime_redefinitions_are_not_typing_overloads(source):
    result=extract_candidate(source,'f')
    assert result['status']=='blocked'
    assert any(i['kind']=='ambiguous-binding' for i in result['issues'])


def test_literal_regex_and_type_metadata_are_reported_without_admission():
    source='''import re as regex
import typing as t
UNUSED = regex.compile(rb"[a-z]+", flags=regex.A | regex.I)
T = t.TypeVar("T", bound="Unknown", covariant=True)
PATTERN = regex.compile("[-_.]+")
def f(x: t.Any):
    return PATTERN.sub("-", x)
'''
    result=extract_candidate(source,'f')
    assert result['status']=='extracted',result
    assert 'UNUSED =' not in result['candidate_source'] and 'T =' not in result['candidate_source']
    assert 'PATTERN = regex.compile' in result['candidate_source']
    assert len(result['preparation_rules'])==2
    assert result['verification_status']=='not-run'

@pytest.mark.parametrize('initialization', [
    'UNUSED = re.compile(make_pattern())',
    'UNUSED = re.compile("x", flags=unknown())',
    'UNUSED = re.compile("x", flags=re.DEBUG)',
    'UNUSED = re.purge()',
    'UNUSED = re.configure("x")',
    're.compile = replacement',
    're.__dict__["compile"] = replacement',
])
def test_unknown_or_mutating_namespace_calls_remain_blocked(initialization):
    source=f'import re\n{initialization}\nPAT = re.compile("x")\ndef f(x): return PAT.match(x)\n'
    assert extract_candidate(source,'f')['status']=='blocked'


def test_unrelated_typevar_with_dynamic_bound_remains_blocked():
    source='import typing as t\nT = t.TypeVar("T", bound=unknown())\ndef f(x: t.Any): return x\n'
    assert extract_candidate(source,'f')['status']=='blocked'


def test_overload_import_must_precede_its_use():
    source='@t.overload\ndef f(x): ...\ndef f(x): return x\nimport typing as t\n'
    assert extract_candidate(source,'f')['status']=='blocked'

@pytest.mark.parametrize('module,body', [
    ('re', 'PAT = first.compile("x")\ndef f(x): return PAT.match(x)'),
    ('typing', '@first.overload\ndef f(x: int) -> int: ...\ndef f(x: int) -> int: return x'),
])
def test_namespace_mutation_through_second_import_alias_is_rejected(module,body):
    source=f'import {module} as first\nimport {module} as second\nsecond.changed = replacement\n{body}\n'
    result=extract_candidate(source,'f')
    assert result['status']=='blocked'
    assert any(i['kind']=='module-mutation' for i in result['issues'])
