"""Cross-module optional values preserve None and payloads, including witnesses."""
import ast
import pytest
from veripy.compatibility import _signature, _type, compare, _snapshot_value, _samples, _materialize

@pytest.mark.parametrize('annotation',['int | None','None | int','Optional[int]'])
def test_optional_shapes(annotation):
    assert _type(ast.parse(annotation,mode='eval').body)==('optional','int')

def test_unrelated_union_stays_unsupported():
    with pytest.raises(ValueError):_type(ast.parse('int | str',mode='eval').body)

def test_optional_default_is_exact():
    assert _signature('def f(x: int | None = None) -> int:\n    return 0\n','f')
    with pytest.raises(ValueError):_signature('def f(x: int | None = True) -> int:\n    return 0\n','f')

def test_unused_typing_import_is_narrow():
    assert _signature('from typing import Union\ndef f(x: int) -> int:\n    return x\n','f')
    for prefix,body in [('from typing import Union','return Union'),('from external import Union','return x')]:
        with pytest.raises(ValueError):_signature(prefix+'\ndef f(x: int) -> int:\n    '+body+'\n','f')

def test_snapshot_and_native_samples_preserve_none_and_payload():
    typ=('optional','int')
    assert _samples(typ)[0] is None
    assert _materialize(None,typ,{}) is None
    assert _materialize(2,typ,{})==2
    assert _snapshot_value('x',typ)=='(if (x).PyNone? then New.PyNone else New.PySome((x).v))'

@pytest.mark.parametrize('change,status',[('identity','proved-compatible'),('payload','behavioral-difference'),('none','behavioral-difference'),('domain','behavioral-difference')])
@pytest.mark.requires_prover('dafny')
def test_checked_optional_product(tmp_path,change,status):
    old='#@ ensures result == x\ndef f(x: int | None = None) -> int | None:\n    return x\n'
    new=old
    if change=='payload':new='#@ ensures (x is None ==> result is None) and (x is not None ==> result == x + 1)\ndef f(x: int | None = None) -> int | None:\n    if x is None:\n        return x\n    return x + 1\n'
    if change=='none':new='#@ ensures result == (0 if x is None else x)\ndef f(x: int | None = None) -> int | None:\n    if x is None:\n        return 0\n    return x\n'
    if change=='domain':new='#@ requires x is not None\n'+old
    a=tmp_path/'old.py';b=tmp_path/'new.py';a.write_text(old);b.write_text(new)
    result=compare(a,b,tmp_path/'check',time_limit=10)
    assert result['status']==status,result
    if change=='identity':assert result['proof']['ok']
    else:assert not result['proof'].get('ok',False) and result.get('witness')

@pytest.mark.parametrize('typ',['tuple[int | None, bool]','list[int | None]'])
@pytest.mark.requires_prover('dafny')
def test_nested_optional_identity(tmp_path,typ):
    source=f'#@ ensures result == x\ndef f(x: {typ}) -> {typ}:\n    return x\n'
    a=tmp_path/'old.py';b=tmp_path/'new.py';a.write_text(source);b.write_text(source)
    result=compare(a,b,tmp_path/'check',time_limit=10)
    assert result['status']=='proved-compatible',result
