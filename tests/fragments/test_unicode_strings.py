"""Native/compiled checks for Unicode strings and literal prefix tuples."""
from pathlib import Path
import random
import subprocess
import pytest
from veripy.backends.dafny import unicode_strings
from veripy.backends.dafny.encoder import encode_module, EncodeError
from veripy.backends.dafny.driver import find_dafny
from veripy.frontend.extract import parse_source
from veripy.difftest.harness import _load_compiled_module, _compiled_member, to_dafny, from_dafny
from veripy.guards.emitter import emit_guarded
from veripy.guards.runtime import PreconditionError

SOURCE = '''#@ ensures result == s.lower()
def lower(s: str) -> str:
    return s.lower()
#@ ensures result == s.strip()
def trim(s: str) -> str:
    return s.strip()
#@ ensures result == (s.startswith("W/") or s.startswith("w/"))
def weak(s: str) -> bool:
    return s.startswith(("W/", "w/"))
'''


def test_unicode_guards_pin_model_configuration(monkeypatch):
    ns={};exec(emit_guarded(SOURCE,parse_source(SOURCE),'strings.py',check_ensures=True),ns)
    assert ns['lower']('ΟΣ')=='ος'
    monkeypatch.setattr(unicode_strings.unicodedata,'unidata_version','changed')
    with pytest.raises(PreconditionError,match='Unicode'):ns['lower']('A')


def test_prefix_tuple_does_not_hide_failing_argument():
    s='#@ ensures True\ndef f(s: str, xs: list[str]) -> bool:\n    return s.startswith(("", xs[0]))\n'
    with pytest.raises(EncodeError,match='literal'):encode_module(s,parse_source(s),'bad.py')


@pytest.mark.skipif(find_dafny() is None,reason='Dafny required')
def test_unicode_model_verifies_and_matches_native(tmp_path):
    encoded=encode_module(SOURCE,parse_source(SOURCE),'strings.py')
    stub=tmp_path/'strings.dfy';stub.write_text(encoded.dafny_source)
    run=subprocess.run([find_dafny(),'verify','--allow-warnings','--verification-time-limit','30',str(stub)],capture_output=True,text=True)
    assert run.returncode==0,run.stdout+run.stderr
    translated=tmp_path/'compiled'
    run=subprocess.run([find_dafny(),'translate','py',str(stub),'--no-verify','--allow-warnings','--output',str(translated)],capture_output=True,text=True)
    assert run.returncode==0,run.stdout+run.stderr
    mod=_load_compiled_module(Path(str(translated)+'-py'))
    lower=_compiled_member(mod.default__,'lower');trim=_compiled_member(mod.default__,'trim');weak=_compiled_member(mod.default__,'weak')
    mappings,cased,ignorable,spaces=unicode_strings.tables()
    samples=['', 'ΟΣ', 'ΟΣΑ', 'AΣ\u0301', 'AΣ\u0301A', 'Σ', 'İ', ' A\u2003', 'W/"x"', 'w/"x"']
    samples += [chr(i) for i in mappings]
    # Every transition-range endpoint, on both sides of sigma.
    for a,b in cased+ignorable:
        for i in {a,b,max(a-1,0),min(b+1,0x10ffff)}:
            if not 0xd800<=i<=0xdfff:
                samples.extend([chr(i)+'Σ','AΣ'+chr(i)+'A','AΣ'+chr(i)+' '])
    samples += [chr(i)+'x'+chr(i) for a,b in spaces for i in range(a,b+1)]
    rng=random.Random(714)
    alphabet='AaΣσςİ\u0345\u0301\u200d._- \t\n😀'
    samples += [''.join(rng.choices(alphabet,k=rng.randrange(25))) for _ in range(1000)]
    for s in samples:
        arg=to_dafny(s,'str')
        assert from_dafny(lower(arg),'str')==s.lower(),repr(s)
        assert from_dafny(trim(arg),'str')==s.strip(),repr(s)
        assert weak(arg)==s.startswith(('W/','w/')),repr(s)
