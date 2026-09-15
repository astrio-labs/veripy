"""Exact pinned regex languages, native edge cases, and dependency drift."""
import itertools
from pathlib import Path
import re
import subprocess
import pytest
from veripy.backends.dafny.regex_strings import PATTERNS
from veripy.backends.dafny.encoder import encode_module,EncodeError
from veripy.backends.dafny.driver import find_dafny
from veripy.frontend.extract import parse_source
from veripy.difftest.harness import _load_compiled_module,to_dafny,from_dafny
from veripy.guards.emitter import emit_guarded
from veripy.guards.runtime import PreconditionError


def source(pattern,flags,method='fullmatch'):
    return ('import re\nR = re.compile('+repr(pattern)+(', re.IGNORECASE' if flags else '')+')\n'
            '#@ ensures True\ndef f(s: str) -> bool:\n    return R.'+method+'(s) is not None\n')


def test_regex_binding_guard():
    s=source(next(p for p,m in PATTERNS.items() if m[0]=="validate"),2)
    ns={};exec(emit_guarded(s,parse_source(s),'regex.py'),ns)
    assert ns['f']('İ')
    ns['R']=re.compile('.*')
    with pytest.raises(PreconditionError,match='regex dependency'):ns['f']('a')


@pytest.mark.parametrize('prefix', ['R = re.compile(".*")\n','re = 7\n','from unknown import re\n','def R():\n    return 1\n'])
def test_regex_dependencies_cannot_be_replaced(prefix):
    s=source(next(p for p,m in PATTERNS.items() if m[0]=="validate"),2)
    s=s.replace('#@ ensures',prefix+'#@ ensures')
    with pytest.raises(EncodeError):encode_module(s,parse_source(s),'bad.py')


@pytest.mark.skipif(find_dafny() is None,reason='Dafny required')
def test_regex_models_match_native_and_verify(tmp_path):
    patterns=[p for p,m in PATTERNS.items() if m[0] in {"validate", "normalized", "separators"}]
    declarations=['import re'];functions=[]
    native=[]
    for i,pattern in enumerate(patterns):
        kind,_,flags=PATTERNS[pattern]
        declarations.append(f'R{i} = re.compile({pattern!r}'+(', re.IGNORECASE' if flags else '')+')')
        if kind=='separators':
            functions.append(f'#@ ensures True\ndef sub(s: str) -> str:\n    return R{i}.sub("-", s)\n')
            native.append(('sub',re.compile(pattern).sub,'str'))
        else:
            for method in ['match','fullmatch']:
                name=f'f{i}{method}'
                functions.append(f'#@ ensures True\ndef {name}(s: str) -> bool:\n    return R{i}.{method}(s) is not None\n')
                native.append((name,getattr(re.compile(pattern,flags),method),'bool'))
    s='\n'.join(declarations+functions)
    encoded=encode_module(s,parse_source(s),'regex.py');stub=tmp_path/'regex.dfy';stub.write_text(encoded.dafny_source)
    run=subprocess.run([find_dafny(),'verify','--allow-warnings','--verification-time-limit','30',str(stub)],capture_output=True,text=True)
    assert run.returncode==0,run.stdout+run.stderr
    dest=tmp_path/'compiled'
    run=subprocess.run([find_dafny(),'translate','py',str(stub),'--no-verify','--allow-warnings','--output',str(dest)],capture_output=True,text=True)
    assert run.returncode==0,run.stdout+run.stderr
    mod=_load_compiled_module(Path(str(dest)+'-py')).default__
    samples=['a--b','ab--c','foo\n','foo\n\n','İıſK','😀','a---b']
    samples += [''.join(chars) for n in range(5) for chars in itertools.product('aA0-._\n',repeat=n)]
    for value in samples:
        arg=to_dafny(value,'str')
        for name,fn,typ in native:
            expected=fn('-',value) if typ=='str' else fn(value) is not None
            assert from_dafny(getattr(mod,name)(arg),typ)==expected,(name,repr(value))


@pytest.mark.parametrize('expression',['R.fullmatch(s) == True','R.fullmatch(s) == R.fullmatch(s)'])
def test_match_objects_are_not_boolean_values_or_structural_values(expression):
    s=source(next(p for p,m in PATTERNS.items() if m[0]=="validate"),2).replace('R.fullmatch(s) is not None',expression)
    with pytest.raises(EncodeError,match='presence checks'):
        encode_module(s,parse_source(s),'bad.py')


def test_strict_end_anchor_is_not_terminal_newline_anchor():
    strict = r"^([A-Z0-9]|[A-Z0-9][A-Z0-9._-]*[A-Z0-9])\Z"
    dollar = strict[:-2] + "$"
    a = source(strict, 2, 'match')
    b = source(dollar, 2, 'match')
    ea = encode_module(a, parse_source(a), 'strict.py').dafny_source
    eb = encode_module(b, parse_source(b), 'dollar.py').dafny_source
    # Check the operational call, not the shared preamble declaration.
    assert 'VRegexValidName(VRegexAnchorText(s))' not in ea
    assert 'VRegexValidName(VRegexAnchorText(s))' in eb
    ns = {}; exec(emit_guarded(a, parse_source(a), 'strict.py'), ns)
    assert ns['f']('A') and not ns['f']('A\n')
    ns['R'] = re.compile(dollar, re.IGNORECASE)
    with pytest.raises(PreconditionError, match='regex dependency'):
        ns['f']('A\n')


def test_nearby_unregistered_strict_pattern_still_rejected():
    text = source(r"^([A-Z0-9]|[A-Z0-9][A-Z0-9._-]*[A-Z0-9])\Z", 0, 'match')
    with pytest.raises(EncodeError):
        encode_module(text, parse_source(text), 'bad.py')
