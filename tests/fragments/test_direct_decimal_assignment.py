from pathlib import Path
import pytest
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.driver import verify_lean_file,find_lean
from veripy.api import verify

SOURCE='''#@ requires i == 0 or not decimal_valid(s)
#@ ensures raised() == (not decimal_valid(s))
#@ ensures not raised() ==> len(result) == 1 and result[0] == int(s)
def convert(s: str, i: int) -> list[int]:
    xs = [99]
    xs[i] = int(s)
    return xs
'''

@pytest.mark.parametrize('backend',['dafny-outcomes','lean'])
@pytest.mark.requires_prover()
def test_failure_precedes_target_bounds_and_success_assigns(tmp_path,backend):
    p=tmp_path/'convert.py';p.write_text(SOURCE)
    r=verify(p,tmp_path/'proof',backend=backend,time_limit=120,keep_artifacts=True)
    assert r['status']=='ok',str(r.get('failures'))[:2000]

@pytest.mark.parametrize('target',['xs[int(index)]','xs[i + 1]','a, b'])
def test_computed_or_multiple_targets_fail_closed(target):
    source=f'#@ ensures True\ndef f(s: str, index: str, i: int) -> int:\n    xs = [0]\n    {target} = int(s)\n    return 0\n'
    with pytest.raises(EncodeError):encode_outcomes(source,parse_source(source),'bad.py')

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_python_lean_error_order_and_unicode(tmp_path):
    ns={};exec(SOURCE,ns)
    encoded=encode_imperative(SOURCE,parse_source(SOURCE),'convert.py')
    model=encoded.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    rows=[]
    for s in ['0',' -2 ','１２','١٢','bad','']:
        for i in [0,7]:
            try:rhs='Except.ok ['+str(ns['convert'](s,i)[0])+']'
            except ValueError:rhs='Except.error VeriPy.Error.value'
            except IndexError:rhs='Except.error VeriPy.Error.index'
            literal='['+','.join(str(ord(c)) for c in s)+']'
            rows.append(f'theorem replay_{len(rows)} : convert {literal} {i} = {rhs} := by rfl')
    p=tmp_path/'replay.lean';p.write_text(model+'\n'+'\n'.join(rows))
    r=verify_lean_file(p,{},time_limit=120,stub_extent=None)
    assert r.ok,r.raw[-3000:]


@pytest.mark.requires_prover('dafny')
def test_empty_decimal_exposes_failure_without_unfolding(tmp_path):
    source = '''#@ requires len(s) == 0
#@ ensures raised()
def empty_decimal(s: str) -> list[int]:
    values = [0]
    values[0] = int(s)
    return values
'''
    path = tmp_path/'empty_decimal.py'
    path.write_text(source)
    result = verify(path, tmp_path/'proof', backend='dafny-outcomes',
                    time_limit=60, keep_artifacts=True)
    assert result['status'] == 'ok', result
