"""Exact decoder scope, dependency drift, and model preconditions."""
import codecs
import subprocess
import types
import urllib.parse
import pytest
from veripy.backends.dafny.encoder import encode_module, EncodeError
from veripy.backends.dafny.driver import find_dafny
from veripy.frontend.extract import parse_source
from veripy.guards.emitter import emit_guarded
from veripy.guards.runtime import PreconditionError

SOURCE = '''from urllib.parse import unquote
#@ requires s.isascii()
#@ requires e == "ascii" or e == "us-ascii" or e == "utf-8" or e == "iso-8859-1"
#@ ensures len(result) <= len(s)
#@ ensures any(s[i] == "%" for i in range(len(s))) or result == s
def f(s: str, e: str) -> str:
    return unquote(s, encoding=e)
'''


def namespace():
    ns = {}
    exec(emit_guarded(SOURCE, parse_source(SOURCE), 'decoder.py'), ns)
    return ns


def test_guard_baseline_and_domain():
    ns = namespace()
    assert ns['f']('%F0%9F%98%80', 'utf-8') == '😀'
    assert ns['f']('%FF', 'ascii') == '�'
    with pytest.raises(PreconditionError): ns['f']('é', 'utf-8')
    with pytest.raises(PreconditionError): ns['f']('abc', 'utf-16')


@pytest.mark.parametrize('target', ['unquote', '_unquote_impl', '_generate_unquoted_parts', '_asciire', '_hexdig', '_hextobyte'])
def test_guard_rejects_transitive_drift(monkeypatch, target):
    ns = namespace()
    if target == 'unquote':
        ns[target] = lambda *a, **k: 'wrong'
    else:
        monkeypatch.setattr(urllib.parse, target, {} if target == '_hextobyte' else None)
    with pytest.raises(PreconditionError, match='dependency'): ns['f']('%41', 'ascii')


def test_guard_rejects_replacement_handler_drift():
    ns = namespace()
    old = codecs.lookup_error('replace')
    try:
        codecs.register_error('replace', lambda error: ('X', error.end))
        with pytest.raises(PreconditionError, match='dependency'): ns['f']('%FF', 'ascii')
    finally:
        codecs.register_error('replace', old)


def test_guard_rejects_builtin_shadowing(monkeypatch):
    ns = namespace()
    monkeypatch.setitem(urllib.parse.__dict__, 'bytes', str)
    with pytest.raises(PreconditionError, match='dependency'): ns['f']('%41', 'ascii')


def test_guard_rejects_changed_defaults(monkeypatch):
    ns = namespace()
    monkeypatch.setattr(urllib.parse.unquote, '__defaults__', ('utf-8', 'ignore'))
    with pytest.raises(PreconditionError, match='dependency'): ns['f']('%FF', 'ascii')


def test_guard_rejects_helper_with_different_globals(monkeypatch):
    ns = namespace()
    helper = urllib.parse._unquote_impl
    clone = types.FunctionType(helper.__code__, dict(helper.__globals__))
    monkeypatch.setattr(urllib.parse, '_unquote_impl', clone)
    with pytest.raises(PreconditionError, match='dependency'): ns['f']('%41', 'ascii')


def test_isascii_binder_does_not_shadow_input():
    source = '#@ ensures result == ascii_index.isascii()\ndef f(ascii_index: str) -> bool:\n    return ascii_index.isascii()\n'
    encode_module(source, parse_source(source), 'ascii.py')
    ns = {}; exec(emit_guarded(source, parse_source(source), 'ascii.py'), ns)
    assert ns['f']('abc') and not ns['f']('é')


@pytest.mark.parametrize('call', ['unquote(s, e)', 'unquote(string=s)', 'unquote(s, encoding=e, errors="ignore")', 'unquote(1)'])
def test_unsupported_calls(call):
    source = SOURCE.replace('unquote(s, encoding=e)', call)
    with pytest.raises(EncodeError): encode_module(source, parse_source(source), 'bad.py')


@pytest.mark.parametrize('extra', ['unquote = 1', 'from other import unquote', 'def unquote(s): return s'])
def test_rebinding_rejected(extra):
    source = SOURCE.replace('#@ requires s.isascii()', extra+'\n#@ requires s.isascii()')
    with pytest.raises(EncodeError): encode_module(source, parse_source(source), 'bad.py')


@pytest.mark.requires_prover('dafny')
def test_verified_length_bound_and_missing_domain_rejected(tmp_path):
    for name, source, succeeds in (
        ('valid', SOURCE, True),
        ('missing_ascii', SOURCE.replace('#@ requires s.isascii()\n', ''), False),
        ('missing_encoding', SOURCE.replace('#@ requires e == "ascii" or e == "us-ascii" or e == "utf-8" or e == "iso-8859-1"\n', ''), False),
    ):
        file = tmp_path/(name+'.dfy')
        file.write_text(encode_module(source, parse_source(source), name+'.py').dafny_source)
        run = subprocess.run([find_dafny(), 'verify', str(file), '--allow-warnings', '--verification-time-limit', '20'], capture_output=True, text=True, timeout=150)
        assert (run.returncode == 0) == succeeds, run.stdout+run.stderr
