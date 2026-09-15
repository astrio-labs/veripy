"""CPython parity and proof obligations for bounded prefix/suffix matching."""
import itertools
from pathlib import Path
import subprocess

import pytest

from veripy.backends.dafny.driver import find_dafny
from veripy.backends.dafny.encoder import EncodeError, encode_module
from veripy.difftest.harness import _compiled_member, _load_compiled_module, to_dafny
from veripy.frontend.extract import parse_source


SOURCE = '''#@ ensures True
def prefix(s: str, p: str, start: int, end: int) -> bool:
    return s.startswith(p, start, end)
#@ ensures True
def suffix(s: str, p: str, start: int, end: int) -> bool:
    return s.endswith(p, start, end)
#@ ensures True
def prefix_start(s: str, p: str, start: int) -> bool:
    return s.startswith(p, start)
#@ ensures True
def suffix_start(s: str, p: str, start: int) -> bool:
    return s.endswith(p, start)
#@ ensures True
def alternatives(s: str, start: int, end: int) -> bool:
    return s.startswith(("W/", "w/", ""), start, end)
#@ ensures not result
def empty_tuple(s: str, start: int, end: int) -> bool:
    return s.endswith((), start, end)
#@ ensures not result
def beyond(s: str) -> bool:
    return s.startswith("", len(s) + 1)
#@ requires 0 <= start <= end <= len(s)
#@ ensures result == (len(p) <= end - start and s[start:start + len(p)] == p)
def bounded_prefix(s: str, p: str, start: int, end: int) -> bool:
    return s.startswith(p, start, end)
#@ requires 0 <= start <= end <= len(s)
#@ ensures result == (len(p) <= end - start and s[end - len(p):end] == p)
def bounded_suffix(s: str, p: str, start: int, end: int) -> bool:
    return s.endswith(p, start, end)
'''


@pytest.mark.parametrize('call', [
    's.startswith("", "1")', 's.endswith("", None)',
    's.startswith("", True)', 's.startswith("", 0, 1, 2)',
    's.startswith(("", 1), 0)', 's.endswith("", start=1)',
])
def test_unmodeled_affix_arguments_are_rejected(call):
    source = '#@ ensures True\ndef f(s: str) -> bool:\n    return ' + call + '\n'
    with pytest.raises(EncodeError):
        encode_module(source, parse_source(source), 'bad.py')


def run_dafny(path, *args):
    result = subprocess.run([find_dafny(), *args, str(path)], capture_output=True, text=True, timeout=120)
    return result


@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_affix_bounds_match_native_and_prove(tmp_path):
    encoded = encode_module(SOURCE, parse_source(SOURCE), 'affixes.py')
    path = tmp_path / 'affixes.dfy'
    path.write_text(encoded.dafny_source)
    result = run_dafny(path, 'verify', '--allow-warnings', '--verification-time-limit', '30')
    assert result.returncode == 0, result.stdout + result.stderr
    dest = tmp_path / 'compiled'
    result = run_dafny(path, 'translate', 'py', '--no-verify', '--allow-warnings', '--output', str(dest))
    assert result.returncode == 0, result.stdout + result.stderr
    compiled = _load_compiled_module(Path(str(dest) + '-py')).default__
    strings = [''.join(v) for n in range(3) for v in itertools.product('aé😀', repeat=n)]
    strings += ['W/"x"', 'w/""', '\0a\0', 'a\u0301']
    patterns = ['', 'a', 'é', '😀', 'aa', 'é😀', 'W/', '\0', '\u0301']
    for s in strings:
        ds = to_dafny(s, 'str')
        bounds = sorted({-10**100, -len(s)-1, -len(s), -1, 0, 1, len(s)-1, len(s), len(s)+1, 10**100})
        assert compiled.beyond(ds) is False
        for start, end in itertools.product(bounds, repeat=2):
            assert compiled.alternatives(ds, start, end) == s.startswith(('W/', 'w/', ''), start, end)
            assert _compiled_member(compiled, 'empty_tuple')(ds, start, end) is False
            for p in patterns:
                dp = to_dafny(p, 'str')
                assert compiled.prefix(ds, dp, start, end) == s.startswith(p, start, end), (s, p, start, end)
                assert compiled.suffix(ds, dp, start, end) == s.endswith(p, start, end), (s, p, start, end)
        for start in bounds:
            for p in patterns:
                dp = to_dafny(p, 'str')
                assert _compiled_member(compiled, 'prefix_start')(ds, dp, start) == s.startswith(p, start)
                assert _compiled_member(compiled, 'suffix_start')(ds, dp, start) == s.endswith(p, start)


@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
@pytest.mark.parametrize('affixes', ['()', '("", "x")'])
def test_tuple_matching_does_not_hide_failing_bound(tmp_path, affixes):
    source = '#@ ensures True\ndef f(s: str, divisor: int) -> bool:\n    return s.startswith(' + affixes + ', 1 // divisor)\n'
    path = tmp_path / 'unsafe.dfy'
    path.write_text(encode_module(source, parse_source(source), 'unsafe.py').dafny_source)
    result = run_dafny(path, 'verify', '--allow-warnings', '--verification-time-limit', '30')
    assert result.returncode != 0
    assert 'precondition' in result.stdout.lower(), result.stdout + result.stderr
