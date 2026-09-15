"""Real local accumulators must remain separate from the returned spec value."""
import pytest
from veripy.api import verify
from veripy.backends.dafny.encoder import encode_module,EncodeError
from veripy.frontend.extract import parse_source

SOURCE='''#@ requires n >= 0
#@ ensures result == n + 1
def f(n: int) -> int:
    result_py = 1
    result = 0
    while result < n:
        #@ invariant 0 <= result <= n
        #@ decreases n - result
        result += 1
    return result + result_py
'''

@pytest.mark.requires_prover('dafny')
def test_local_result_and_postcondition_are_distinct(tmp_path):
 path=tmp_path/'source.py';path.write_text(SOURCE)
 r=verify(path,tmp_path/'proof',backend='dafny',time_limit=20,keep_artifacts=True)
 assert r['status']=='ok',r
 from veripy.guards.emitter import emit_guarded
 ns={};exec(emit_guarded(SOURCE,parse_source(SOURCE),'source.py'),ns)
 assert ns['f'](4)==5


@pytest.mark.requires_prover('dafny')
def test_wrong_return_is_not_hidden_by_local_result(tmp_path):
 path=tmp_path/'source.py';path.write_text(SOURCE.replace('return result + result_py','return result'))
 r=verify(path,tmp_path/'proof',backend='dafny',time_limit=20,keep_artifacts=True)
 assert r['status']=='failed',r


def test_result_parameter_stays_rejected():
 source='#@ ensures result == 1\ndef f(result: int) -> int:\n    return 1\n'
 with pytest.raises(EncodeError,match='parameter'):encode_module(source,parse_source(source),'s.py')


@pytest.mark.requires_prover('dafny')
def test_module_constant_cannot_replace_postcondition_result(tmp_path):
 source='result = 1\n#@ ensures result == 1\ndef f() -> int:\n    return 0\n'
 path=tmp_path/'source.py';path.write_text(source)
 report=verify(path,tmp_path/'proof',backend='dafny',time_limit=20,keep_artifacts=True)
 assert report['status']=='failed',report
 assert any(f['kind']=='postcondition' for f in report['failures'])
