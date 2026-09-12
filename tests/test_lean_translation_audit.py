"""Independent finite execution oracles for admitted control flow and ownership."""
import itertools
import pytest
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.driver import find_lean, verify_lean_file
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.encoder import EncodeError

PROGRAM='''#@ ensures True
def first_positive(xs: list[int], d: int) -> bool:
    return len(xs) > 0 and xs[0] // d > 0

#@ ensures True
def select(xs: list[int], i: int) -> int:
    return xs[i]

#@ ensures result >= 0
def scan(rows: list[list[int]]) -> int:
    count = 0
    for row in rows:
        #@ invariant count >= 0
        for item in row:
            #@ invariant count >= 0
            if item < 0:
                continue
            if item == 0:
                break
            count += 1
    return count
'''

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_composed_control_flow_against_cpython(tmp_path):
    namespace={};exec(PROGRAM,namespace)
    encoded=encode_imperative(PROGRAM,parse_source(PROGRAM),'audit.py')
    model=encoded.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    def lit(v):
        if isinstance(v,list):return '['+','.join(lit(x) for x in v)+']'
        return '('+str(v)+')'
    commands=[]
    cases=[]
    for xs,d in itertools.product([[],[-2],[0],[2]],[0,-2,2]):cases.append(('first_positive',[xs,d]))
    for xs,i in itertools.product([[],[4],[4,7]],range(-3,4)):cases.append(('select',[xs,i]))
    for rows in itertools.product([[],[-1,2],[0,2],[2,-1,3],[2,0,3]],repeat=2):cases.append(('scan',[list(rows)]))
    for n,(name,args) in enumerate(cases):
        try:
            value=namespace[name](*args)
            rhs='Except.ok '+(str(value).lower() if isinstance(value,bool) else lit(value))
        except IndexError:rhs='Except.error VeriPy.Error.index'
        except ZeroDivisionError:rhs='Except.error VeriPy.Error.zero'
        commands.append(f'theorem audit_{n} : {name} '+ ' '.join(lit(a) for a in args)+' = '+rhs+' := by rfl\n#print axioms audit_'+str(n))
    artifact=tmp_path/'audit.lean';artifact.write_text(model+'\n'+'\n'.join(commands))
    result=verify_lean_file(artifact,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw

@pytest.mark.parametrize('body',[
 'ys = xs\n    ys.append(3)\n    return len(xs)',
 'xs.append(3)\n    return len(xs)',
])
def test_borrowed_list_mutation_is_rejected(body):
    source='#@ ensures True\ndef wrong(xs: list[int]) -> int:\n    '+body+'\n'
    with pytest.raises(EncodeError):encode_imperative(source,parse_source(source),'bad.py')
