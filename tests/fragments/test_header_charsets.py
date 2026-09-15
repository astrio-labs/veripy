import json,itertools,subprocess
from pathlib import Path
import pytest,re
from veripy.backends.dafny.header_charsets import PATTERN,FLAGS
from veripy.backends.dafny.encoder import encode_module,EncodeError
from veripy.frontend.extract import parse_source
from veripy.guards.emitter import emit_guarded
from veripy.guards.runtime import PreconditionError
from veripy.backends.dafny.driver import find_dafny
from veripy.difftest.harness import _load_compiled_module,to_dafny,from_dafny

SOURCE=f'''import re
pattern = re.compile({PATTERN!r}, re.ASCII | re.VERBOSE)
#@ ensures True
def f(s: str) -> tuple[bool, str, str]:
    match = pattern.match(s)
    if match:
        encoding, value = match.groups()
        return True, encoding, value
    return False, "", ""
'''

@pytest.mark.requires_prover('dafny')
def test_closed_capture_model_native_compiled(tmp_path):
 encoded=encode_module(SOURCE,parse_source(SOURCE),'source.py');stub=tmp_path/'source.dfy';stub.write_text(encoded.dafny_source)
 for cmd in ([find_dafny(),'verify',str(stub),'--allow-warnings','--verification-time-limit','30'],[find_dafny(),'translate','py',str(stub),'--no-verify','--allow-warnings','--output',str(tmp_path/'compiled')]):
  r=subprocess.run(cmd,capture_output=True,text=True,timeout=180);assert r.returncode==0,r.stdout+r.stderr
 compiled=_load_compiled_module(tmp_path/'compiled-py').default__
 ns={};exec(emit_guarded(SOURCE,parse_source(SOURCE),'source.py'),ns)
 regex=re.compile(PATTERN,FLAGS)
 samples=["UTF-8''caf%C3%A9", "''x'", "utf-8'en'hello tail", "UTF-8''", "''%ff", "é''x", "ascii''é", "ascii''aé", "ascii''a\nx", "''a=bad"]
 samples += [''.join(s) for n in range(6) for s in itertools.product("a' %=",repeat=n)]
 for s in samples:
  match=regex.match(s);expected=(True,*match.groups()) if match else (False,'','')
  actual=compiled.f(to_dafny(s,'str'));actual=(actual[0],from_dafny(actual[1],'str'),from_dafny(actual[2],'str'))
  assert actual==ns['f'](s)==expected,repr(s)
 ns['pattern']=re.compile(PATTERN,re.VERBOSE)
 with pytest.raises(PreconditionError):ns['f']("''x")

@pytest.mark.parametrize('operation',["pattern.fullmatch(s)","pattern.match(s, 0)","pattern.match(s=s)"])
def test_unsupported_calls_rejected(operation):
 source=SOURCE.replace('pattern.match(s)',operation)
 with pytest.raises(EncodeError):encode_module(source,parse_source(source),'source.py')

def test_match_equality_not_structural():
 source=SOURCE.replace('if match:', 'if match == pattern.match(s):')
 with pytest.raises(EncodeError):encode_module(source,parse_source(source),'source.py')

@pytest.mark.parametrize('flags', ['re.VERBOSE', 're.ASCII', 're.ASCII | re.VERBOSE | re.IGNORECASE'])
def test_changed_flags_rejected(flags):
 source=SOURCE.replace('re.ASCII | re.VERBOSE', flags)
 with pytest.raises(EncodeError):encode_module(source,parse_source(source),'source.py')

@pytest.mark.parametrize('replacement', ['pattern = re.compile(".*")', 're = object()', 'from unknown import re'])
def test_rebound_dependencies_rejected(replacement):
 source=SOURCE.replace('#@ ensures True', replacement+'\n#@ ensures True')
 with pytest.raises(EncodeError):encode_module(source,parse_source(source),'source.py')
