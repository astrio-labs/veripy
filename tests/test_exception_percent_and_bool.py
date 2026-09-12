from pathlib import Path
import pytest
from veripy.api import verify
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.driver import verify_lean_file,find_lean

FORMAT='''#@ requires len(s) == 1
#@ ensures raised()
def reject(s: str) -> int:
    raise ValueError("Invalid %% separator: %c" % s)
'''
BOOL='''#@ ensures result == x + (1 if flag else 0)
def increment(x: int, flag: bool) -> int:
    value = x
    value += flag
    return value
'''

@pytest.mark.parametrize('backend',['dafny-outcomes','lean'])
@pytest.mark.parametrize('source',[FORMAT,BOOL])
def test_positive_contracts(tmp_path,backend,source):
    path=tmp_path/'source.py';path.write_text(source)
    result=verify(path,tmp_path/'proof',backend=backend,time_limit=120,keep_artifacts=True)
    assert result['status']=='ok',str(result.get('failures'))[:1600]

@pytest.mark.parametrize('backend',['dafny-outcomes','lean'])
def test_format_failure_not_erased(tmp_path,backend):
    source=FORMAT.replace('#@ requires len(s) == 1\n','')
    path=tmp_path/'source.py';path.write_text(source)
    result=verify(path,tmp_path/'proof',backend=backend,time_limit=120,keep_artifacts=True)
    assert result['status']=='failed',result
    assert not any(any(marker in e.get('message','').lower() for marker in ['time limit','type mismatch','unexpected token']) for e in result.get('failures',[]))

@pytest.mark.parametrize('format_text',['%s','%2c','%c%c','%(x)c','%','%%'])
def test_other_formats_fail_closed(format_text):
    source=FORMAT.replace('Invalid %% separator: %c',format_text)
    with pytest.raises(EncodeError):encode_outcomes(source,parse_source(source),'bad.py')

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_kernel_format_errors_and_integer_increment(tmp_path):
    source=FORMAT+BOOL
    namespace={};exec(source,namespace)
    model=encode_imperative(source,parse_source(source),'replay.py').lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    commands=[]
    for s in ['', 'a', 'ab', '🙂','\n']:
        try:namespace['reject'](s);assert False
        except ValueError:tag='value'
        except TypeError:tag='type'
        literal='['+','.join(str(ord(c)) for c in s)+']'
        commands.append(f'theorem error_{len(commands)} : reject {literal} = Except.error VeriPy.Error.{tag} := by rfl')
    for n in [-3,0,9]:
        for b in [False,True]:
            result=namespace['increment'](n,b)
            commands.append(f'theorem plus_{len(commands)} : increment ({n}) {str(b).lower()} = Except.ok ({result}) := by rfl')
    path=tmp_path/'replay.lean';path.write_text(model+'\n'+'\n'.join(commands))
    result=verify_lean_file(path,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw[-2500:]
