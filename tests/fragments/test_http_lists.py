import ast,itertools,re,subprocess
from pathlib import Path
import pytest
from veripy.backends.dafny.encoder import encode_module,EncodeError
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.http_lists import signature,_reference_parse_http_list
from veripy.guards.emitter import emit_guarded
from veripy.guards.runtime import PreconditionError,TypeGuardError
from veripy.backends.dafny.driver import find_dafny
from veripy.difftest.harness import _load_compiled_module,to_dafny,from_dafny
from urllib.request import parse_http_list

SOURCE='''from urllib.request import parse_http_list as parse_fields
#@ ensures True
def f(s: str) -> list[str]:
    return parse_fields(s)
'''

def test_dependency_fingerprint_and_drift():
 assert signature(parse_http_list)==signature(_reference_parse_http_list)
 ns={};exec(emit_guarded(SOURCE,parse_source(SOURCE),'header.py'),ns)
 assert ns['f']('a, "b,c"')==['a','"b,c"']
 ns['parse_fields']=lambda s:[]
 with pytest.raises(PreconditionError,match='dependency'):ns['f']('a')

@pytest.mark.parametrize('extra',['parse_fields = unknown\n','def parse_fields(s): return []\n','from other import parse_fields\n'])
def test_import_shadowing_rejected(extra):
 text=SOURCE.replace('#@ ensures',extra+'#@ ensures')
 with pytest.raises(EncodeError):encode_module(text,parse_source(text),'header.py')

@pytest.mark.parametrize('replacement',['parse_fields(s, s)','parse_fields(s=s)','parse_fields(3)'])
def test_call_boundary_rejected(replacement):
 text=SOURCE.replace('parse_fields(s)',replacement)
 with pytest.raises(EncodeError):encode_module(text,parse_source(text),'header.py')


@pytest.mark.requires_prover('dafny')
def test_dependency_model_agrees_with_compiled_python(tmp_path):
 encoded=encode_module(SOURCE,parse_source(SOURCE),'header.py');stub=tmp_path/'header.dfy';stub.write_text(encoded.dafny_source)
 for command in ([find_dafny(),'verify',str(stub),'--allow-warnings','--verification-time-limit','30'],[find_dafny(),'translate','py',str(stub),'--no-verify','--allow-warnings','--output',str(tmp_path/'compiled')]):
  r=subprocess.run(command,capture_output=True,text=True,timeout=120);assert r.returncode==0,r.stdout+r.stderr
 compiled=_load_compiled_module(tmp_path/'compiled-py').default__
 samples=['',' ', 'a,','"a,b", c','"a\\"b"','a\\,b','"unfinished\\','\u2003x\u2003','😀,é']
 samples+=[''.join(x) for n in range(5) for x in itertools.product('a, "\\',repeat=n)]
 for s in samples:assert from_dafny(compiled.f(to_dafny(s,'str')),('list','str'))==parse_http_list(s),repr(s)

def test_scalar_boundary_and_callable_metadata():
 from types import FunctionType
 ns={};exec(emit_guarded(SOURCE,parse_source(SOURCE),'header.py'),ns)
 for s in ('\ud800','x\udfff'):
  with pytest.raises(TypeGuardError):ns['f'](s)
 replacement=FunctionType(parse_http_list.__code__,parse_http_list.__globals__,argdefs=('changed',))
 ns['parse_fields']=replacement
 with pytest.raises(PreconditionError,match='dependency'):ns['f']('a')


def test_model_names_cannot_be_forged():
 from veripy.backends.dafny.encoder import _preamble_clash
 assert _preamble_clash('VHeaderFields')


@pytest.mark.requires_prover('dafny')
def test_character_string_comparison_matches_python(tmp_path):
 from veripy.api import verify
 source='''#@ requires len(s) >= 2
#@ ensures result == (s[:1] == s[-1:] and s[-1:] == target)
def f(s: str, target: str) -> bool:
    return s[0] == s[-1] == target
'''
 path=tmp_path/'source.py';path.write_text(source)
 result=verify(path,tmp_path/'proof',backend='dafny',time_limit=20,keep_artifacts=True)
 assert result['status']=='ok',result
 encoded=encode_module(source,parse_source(source),'source.py');stub=tmp_path/'source.dfy';stub.write_text(encoded.dafny_source)
 r=subprocess.run([find_dafny(),'translate','py',str(stub),'--no-verify','--allow-warnings','--output',str(tmp_path/'compiled')],capture_output=True,text=True,timeout=120);assert r.returncode==0,r.stdout+r.stderr
 compiled=_load_compiled_module(tmp_path/'compiled-py').default__
 for s in ('aa','ab','😀x😀'):
  for target in ('','a','aa','b','😀'):
   assert compiled.f(to_dafny(s,'str'),to_dafny(target,'str'))==(s[0]==s[-1]==target)


def test_postponed_annotations_preserve_verbatim_island(tmp_path):
 from veripy.guards.runtime import verify_island_integrity
 source='"""Original module documentation."""\nfrom __future__ import annotations\n'+SOURCE
 guarded=emit_guarded(source,parse_source(source),'header.py')
 ns={};exec(guarded,ns)
 assert ns['__doc__']=='Original module documentation.'
 assert ns['f']('a, "b,c"')==['a','"b,c"']
 assert source.rstrip('\n') in guarded
 path=tmp_path/'guarded.py';path.write_text(guarded)
 assert verify_island_integrity(path)
