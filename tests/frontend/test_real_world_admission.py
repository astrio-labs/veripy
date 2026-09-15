"""Regressions found by preserving released upstream Python bodies."""
from pathlib import Path

import pytest

from veripy.api import verify
from veripy.backends.dafny.driver import find_dafny
from veripy.backends.dafny.encoder import EncodeError, encode_module
from veripy.difftest.harness import difftest_file
from veripy.frontend.extract import parse_source


def encode(source):
    return encode_module(source, parse_source(source), 'case.py')


DIVMOD = '''#@ requires b != 0
#@ ensures result == (a // b, a % b)
def quotient_remainder(a: int, b: int) -> tuple[int, int]:
    q, r = divmod(a, b)
    return q, r
'''


@pytest.mark.parametrize('source', [
    DIVMOD.replace('def quotient_remainder(a:', 'def quotient_remainder(divmod: int, a:'),
    'divmod = 7\n' + DIVMOD,
    'def divmod(a, b):\n    return 0, 0\n' + DIVMOD,
    DIVMOD.replace('    q, r', '    divmod = 1\n    q, r'),
])
def test_divmod_shadowing_fails_closed(source):
    with pytest.raises(EncodeError, match='shadows a builtin'):
        encode(source)


@pytest.mark.parametrize('expr', ['divmod(a)', 'divmod(a, b, 1)', 'divmod(a, b=b)',
                                 'divmod(True, b)', 'divmod("1", b)', 'divmod(1.5, b)'])
def test_divmod_unsupported_operands_rejected(expr):
    source = '#@ ensures True\ndef f(a: int, b: int) -> tuple[int, int]:\n    return ' + expr + '\n'
    with pytest.raises(EncodeError):
        encode(source)


def test_private_names_do_not_collide_with_other_methods_or_locals():
    source = '''#@ ensures result == x + 1
def _f(x: int) -> int:
    _local = x + 1
    return _local

#@ ensures result == x - 1
def py_f(x: int) -> int:
    return x - 1
'''
    result = encode(source)
    assert len(set(result.method_names.values())) == 2
    assert not result.method_names['_f'].startswith('_')
    assert result.method_names['py_f'] == 'py_f'


@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_divmod_requires_nonzero_divisor_and_matches_python(tmp_path: Path):
    path = tmp_path / 'division.py'
    path.write_text(DIVMOD)
    assert verify(path, tmp_path / 'proof')['status'] == 'ok'
    diff = difftest_file(path, tmp_path / 'diff', examples=120)
    assert diff.ok, diff
    path.write_text(DIVMOD.replace('#@ requires b != 0\n', ''))
    result = verify(path, tmp_path / 'bad')
    assert result['status'] == 'failed', result
    assert any(f['kind'] == 'call-precondition' for f in result['failures']), result


@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_private_function_and_local_execute_through_name_mapping(tmp_path: Path):
    path = tmp_path / 'private.py'
    path.write_text('''#@ ensures result == x + 1
def _f(x: int) -> int:
    _local = x + 1
    return _local

#@ ensures result == x - 1
def py_f(x: int) -> int:
    return x - 1
''')
    assert verify(path, tmp_path / 'proof')['status'] == 'ok'
    diff = difftest_file(path, tmp_path / 'diff', examples=60)
    assert diff.ok, diff
    assert len(diff.functions) == 2
