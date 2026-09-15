"""Admission and Python fidelity for the padding optimizer's new syntax."""
import pytest
from veripy.api import verify
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.guards.outcomes import emit_outcome_guarded
from veripy.guards.runtime import TypeGuardError

SOURCE='''#@ ensures not raised()
#@ ensures result == (n if n is not None else 3)
def f(*, n: int | None = None) -> int:
    return n if n is not None else 3
'''

@pytest.mark.requires_prover('dafny')
def test_optional_keyword_default_proved_and_guarded(tmp_path):
    p=tmp_path/'default.py';p.write_text(SOURCE)
    r=verify(p,tmp_path/'proof',backend='dafny-outcomes',time_limit=15)
    assert r['status']=='ok',r
    ns={};exec(emit_outcome_guarded(SOURCE,parse_source(SOURCE),'default.py',check_ensures=True),ns)
    assert ns['f']()==3
    for v in [None,-7,0,9,10**80]:assert ns['f'](n=v)==(3 if v is None else v)
    with pytest.raises(TypeGuardError):ns['f'](n=True)
    with pytest.raises(TypeError):ns['f'](2)

@pytest.mark.parametrize('signature',['n: int = None','n: list[int] = []','n: int | None = int("3")'])
def test_nonadmitted_defaults_rejected(signature):
    s='#@ ensures True\ndef f(*, '+signature+') -> int:\n    return 1\n'
    with pytest.raises(EncodeError):encode_outcomes(s,parse_source(s),'bad.py')

@pytest.mark.parametrize('expression',['n if n is not None else 3','3 if n is None else n'])
@pytest.mark.requires_prover('dafny')
def test_optional_conditional_matches_compiled_python(tmp_path,expression):
    from veripy.difftest.harness import difftest_file
    s=f'#@ ensures result == ({expression})\ndef f(n: int | None) -> int:\n    return {expression}\n'
    p=tmp_path/'choice.py';p.write_text(s)
    assert verify(p,tmp_path/'proof',time_limit=15)['status']=='ok'
    assert difftest_file(p,tmp_path/'diff',examples=50).ok

MESSAGE='''#@ ensures raised() == (len(xs) == 0)
#@ ensures not raised() ==> result == len(xs)
def f(xs: list[int]) -> int:
    if not xs:
        raise ValueError(f"bad: {list(xs)!r}")
    return len(xs)
'''

@pytest.mark.requires_prover('dafny')
def test_exact_integer_list_error_message_preserved(tmp_path):
    p=tmp_path/'message.py';p.write_text(MESSAGE)
    assert verify(p,tmp_path/'proof',backend='dafny-outcomes',time_limit=15)['status']=='ok'
    ns={};exec(emit_outcome_guarded(MESSAGE,parse_source(MESSAGE),'message.py',check_ensures=True),ns)
    with pytest.raises(ValueError,match=r'bad: \[\]'):ns['f']([])
    assert ns['f']([1,2])==2

@pytest.mark.parametrize('source',[
 MESSAGE.replace('xs: list[int]','xs: list[str]'),
 MESSAGE.replace('list(xs)!r','list(xs):x'),
 MESSAGE.replace('list(xs)!r','list(xs, xs)!r'),
 MESSAGE.replace('def f(xs:', 'def f(list: int, xs:'),
 'from math import prod as list\n'+MESSAGE,
 MESSAGE.replace('    if not xs:', '    list = 1\n    if not xs:'),
])
def test_message_repr_unsafe_forms_rejected(source):
    with pytest.raises(EncodeError):encode_outcomes(source,parse_source(source),'bad.py')
