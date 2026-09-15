"""Propagation, ordered handlers, and exact named exception outcomes."""
from pathlib import Path
import subprocess
import pytest
from veripy.api import verify
from veripy.backends.dafny.driver import find_dafny
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.frontend.extract import parse_source
from veripy.guards.outcomes import emit_outcome_guarded
from veripy.difftest.harness import _load_compiled_module

SOURCE='''class InvalidFormat(ValueError):
    pass
class InvalidChecksum(ValueError):
    pass
#@ ensures raised("InvalidFormat") == (x < 0)
#@ ensures raised() == (x < 0)
#@ ensures not raised() ==> result == x
def base(x: int) -> int:
    if x < 0:
        raise InvalidFormat()
    return x
#@ ensures raised() == (x < 0)
#@ ensures raised("InvalidChecksum") == (x < 0)
#@ ensures not raised() ==> result == x
def validate(x: int) -> int:
    try:
        value = base(x)
    except InvalidFormat:
        raise InvalidChecksum()
    return value
#@ ensures not raised()
#@ ensures result == (x >= 0)
def valid(x: int) -> bool:
    try:
        return bool(validate(x) + 1)
    except ValueError:
        return False
'''


@pytest.mark.skipif(find_dafny() is None,reason='Dafny required')
def test_tagged_calls_prove_and_preserve_exception_types(tmp_path):
    p=tmp_path/'errors.py';p.write_text(SOURCE)
    report=verify(p,tmp_path/'proof',backend='dafny-outcomes',time_limit=30,keep_artifacts=True)
    assert report['status']=='ok',report
    ns={};exec(emit_outcome_guarded(SOURCE,parse_source(SOURCE),'errors.py',check_ensures=True),ns)
    for x in range(-10,11):
        assert ns['valid'](x)==(x>=0)
        if x<0:
            with pytest.raises(ns['InvalidChecksum']):ns['validate'](x)
        else:assert ns['validate'](x)==x
    dest=tmp_path/'compiled'
    r=subprocess.run([find_dafny(),'translate','py',report['stub'],'--no-verify','--allow-warnings','--output',str(dest)],capture_output=True,text=True)
    assert r.returncode==0,r.stdout+r.stderr
    compiled=_load_compiled_module(Path(str(dest)+'-py')).default__
    for x in range(-10,11):assert compiled.valid(x)==(x>=0,0)


def test_guard_preserves_eager_annotations_and_explicit_future():
    from veripy.guards.outcomes import emit_outcome_guarded
    from veripy.frontend.extract import parse_source
    body='#@ ensures not raised()\ndef f(x: int) -> int:\n    return x\n'
    for future in [False,True]:
        source=('from __future__ import annotations\n' if future else '')+body
        generated=emit_outcome_guarded(source,parse_source(source),'annotations.py')
        namespace={};exec(generated,namespace)
        assert namespace['f'].__annotations__['x']==('int' if future else int)
        assert namespace['f'](7)==7



def test_unused_collateral_union_import_is_not_type_admission():
    from veripy.backends.dafny.encoder import EncodeError
    source = 'from typing import Tuple, Union\n#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n'
    encode_outcomes(source, parse_source(source))
    for changed in [source.replace('return x', 'return Union'),
                    source.replace('x: int', 'x: "Union[int, str]"')]:
        with pytest.raises(EncodeError, match='supported unaliased names'):
            encode_outcomes(changed, parse_source(changed))
