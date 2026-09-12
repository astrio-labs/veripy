"""Kernel/native checks for modeled exception classes and bounded handlers."""
from pathlib import Path
import pytest
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.driver import find_lean, verify_lean_file
from veripy.backends.dafny.encoder import EncodeError
from veripy.frontend.extract import parse_source

HEADER='from stdnum.exceptions import ValidationError, InvalidFormat, InvalidChecksum\n'
SOURCE=HEADER+'''
#@ ensures True
def reject(n: int) -> int:
    if n == 0:
        raise InvalidFormat()
    if n == 1:
        raise InvalidChecksum()
    if n == 2:
        raise ValueError()
    if n == 4:
        return 1 // (n - 4)
    return n

#@ ensures True
def caught(n: int) -> int:
    try:
        return reject(n)
    except ValidationError:
        return -1

#@ ensures True
def converted(n: int) -> int:
    try:
        v = reject(n)
    except Exception:
        raise InvalidFormat()
    return v + 1

#@ ensures True
def handler_error(n: int) -> int:
    try:
        return reject(n)
    except ValidationError:
        raise ValueError()
#@ ensures True
def format_only(n: int) -> int:
    try:
        return reject(n)
    except InvalidFormat:
        return -2
'''

def native_namespace(source):
    # Execute the source with a real Python hierarchy matching the explicit
    # dependency model; no dependency installation needed by compiler tests.
    class ValidationError(ValueError):pass
    class InvalidFormat(ValidationError):pass
    class InvalidChecksum(ValidationError):pass
    ns=dict(ValidationError=ValidationError,InvalidFormat=InvalidFormat,InvalidChecksum=InvalidChecksum)
    exec(source.replace(HEADER,''),ns)
    return ns

def literal(value):
    if type(value) is bool:return 'true' if value else 'false'
    if isinstance(value,str):return '['+','.join(str(ord(c)) for c in value)+']'
    return '('+str(value)+')'

def kernel_checks(source,cases,tmp_path):
    ns=native_namespace(source)
    encoded=encode_imperative(source,parse_source(source),'exceptions.py')
    model=encoded.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    tags={'ValueError':'VeriPy.Error.value','InvalidChecksum':'(VeriPy.Error.custom 2)',
          'InvalidFormat':'(VeriPy.Error.custom 3)','ValidationError':'(VeriPy.Error.custom 4)', 'ZeroDivisionError':'VeriPy.Error.zero'}
    commands=[]
    for i,(name,args) in enumerate(cases):
        try:rhs='Except.ok '+literal(ns[name](*args))
        except (ValueError, ZeroDivisionError) as exc:rhs='Except.error '+tags[type(exc).__name__]
        commands.append(f'theorem replay_{i} : {name} '+' '.join(literal(x) for x in args)+' = '+rhs+f' := by rfl\n#print axioms replay_{i}')
    artifact=tmp_path/'replay.lean';artifact.write_text(model+'\n'+'\n'.join(commands))
    result=verify_lean_file(artifact,{},time_limit=180,stub_extent=None)
    assert result.ok,result.raw[-8000:]

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_inheritance_conversion_and_handler_propagation(tmp_path):
    kernel_checks(SOURCE,[(n,[v]) for n in ['reject','caught','converted','handler_error','format_only'] for v in range(5)],tmp_path)

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_luhn_all_outcomes(tmp_path):
    source=(Path(__file__).resolve().parents[1]/'case_studies/luhn_validation_v1/luhn.py').read_text()
    cases=[(name,[s,a]) for name in ['checksum','validate','is_valid','calc_check_digit']
           for a in ['0123456789','ab','aabc','αβγ']
           for s in ['',a[0],a[1]*2,a+'?', '79927398713']]
    kernel_checks(source,cases,tmp_path)

@pytest.mark.parametrize('body',[
    'try:\n        v = reject(n)\n        v = v + 1\n    except ValidationError:\n        return -1\n    return v',
    'try:\n        return reject(n)\n    except ValidationError as error:\n        return -1',
    'try:\n        return reject(n)\n    except ValidationError:\n        return -1\n    finally:\n        n = n + 1',
    'v = 0\n    try:\n        v = reject(n)\n    except ValidationError:\n        raise InvalidFormat()\n    return v',
])
def test_unsupported_stateful_handlers_fail_closed(body):
    source=SOURCE+'\n#@ ensures True\ndef unsupported(n: int) -> int:\n    '+body+'\n'
    with pytest.raises(EncodeError):encode_imperative(source,parse_source(source),'unsupported.py')
