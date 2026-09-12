"""Independent Python/kernel checks for immutable sequence lowering."""
import itertools
from pathlib import Path
import pytest
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.driver import find_lean, verify_lean_file
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.encoder import EncodeError

SOURCE = '''#@ ensures True
def checksum(number: str, alphabet: str) -> int:
    n = len(alphabet)
    values = tuple(alphabet.index(i) for i in reversed(str(number)))
    return (sum(values[::2]) + sum(sum(divmod(i * 2, n)) for i in values[1::2])) % n

#@ ensures True
def lookup(s: str, needle: str) -> int:
    return s.index(needle)

#@ ensures True
def selected(xs: list[int], lo: int, hi: int) -> int:
    values = tuple(x for x in xs)
    return sum(values[lo:hi:2])
'''

@pytest.mark.skipif(find_lean() is None, reason='Lean unavailable')
def test_sequences_match_python_kernel(tmp_path):
    namespace={};exec(SOURCE,namespace)
    encoded=encode_imperative(SOURCE,parse_source(SOURCE),'sequences.py')
    model=encoded.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    def lit(v):
        if isinstance(v,str):return '['+','.join(str(ord(c)) for c in v)+']'
        if isinstance(v,list):return '['+','.join(lit(x) for x in v)+']'
        return '('+str(v)+')'
    cases=[('checksum',[s,a]) for s,a in itertools.product(['','0','12','79927398713','123a','é'],['0123456789','01','', 'aba'])]
    cases += [('lookup',[s,n]) for s,n in itertools.product(['','ababa','é🙂é'],['','a','aba','x','🙂'])]
    cases += [('selected',[[1,2,3,4,5],lo,hi]) for lo,hi in itertools.product([-7,-2,0,2,7],[-7,-1,0,4,8])]
    commands=[]
    for i,(name,args) in enumerate(cases):
        try: rhs='Except.ok '+lit(namespace[name](*args))
        except ValueError:rhs='Except.error VeriPy.Error.value'
        except ZeroDivisionError:rhs='Except.error VeriPy.Error.zero'
        commands.append(f'theorem sequence_{i} : {name} '+' '.join(lit(a) for a in args)+' = '+rhs+f' := by rfl\n#print axioms sequence_{i}')
    artifact=tmp_path/'sequences.lean';artifact.write_text(model+'\n'+'\n'.join(commands))
    result=verify_lean_file(artifact,{},time_limit=180,stub_extent=None)
    assert result.ok,result.raw

@pytest.mark.parametrize('step',['0','-1','step'])
def test_unsupported_strides_fail_closed(step):
    source=f'#@ ensures True\ndef f(xs: list[int], step: int) -> int:\n    return sum(xs[::{step}])\n'
    with pytest.raises(EncodeError):encode_imperative(source,parse_source(source),'bad.py')

@pytest.mark.parametrize('body', [
    't = tuple(x for x in xs)\n    return t == xs',
    'r = reversed(xs)\n    a = tuple(r)\n    b = tuple(r)\n    return a == b',
])
def test_tuple_type_and_iterator_lifetime_not_erased(body):
    source = '#@ ensures True\ndef f(xs: list[int]) -> bool:\n    '+body+'\n'
    with pytest.raises(EncodeError):
        encode_imperative(source,parse_source(source),'boundary.py')
