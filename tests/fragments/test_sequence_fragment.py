"""Python fidelity and ownership boundaries for shard-search operations."""
import pytest
from veripy.api import verify
from veripy.backends.dafny.encoder import encode_module, EncodeError
from veripy.backends.dafny.driver import find_dafny
from veripy.difftest.harness import difftest_file
from veripy.frontend.extract import parse_source


def encode(s):
    return encode_module(s, parse_source(s), 'sequence.py')

SORT = '''#@ ensures len(result) == len(xs)
#@ ensures forall j in range(len(result) - 1) :: result[j][0] <= result[j+1][0]
def f(xs: list[tuple[int,int]]) -> list[tuple[int,int]]:
    local = [v for v in xs]
    local.sort()
    return local
'''
KEY = '''#@ ensures len(result) == len(xs)
def f(xs: list[int]) -> list[int]:
    order = sorted(range(len(xs)), key=lambda i: (xs[i], *(xs[d] for d in range(i) if d != i)))
    return order
'''
BISECT = '''from bisect import bisect_right, insort
#@ ensures len(result) <= len(xs) + 1
def f(xs: list[tuple[int,int]], x: tuple[int,int]) -> list[tuple[int,int]]:
    local = [v for v in xs]
    local.sort()
    cutoff = bisect_right(local, x)
    if cutoff:
        del local[:cutoff]
    insort(local, x)
    return local
'''
OPTIONAL = '''#@ ensures result == (x[0] if x is not None else 0)
def f(x: tuple[int,int] | None) -> int:
    if x:
        return x[0]
    return 0
'''
READONLY = '''#@ ensures result == len(xs)
def size(xs: list[int]) -> int:
    return len(xs)
#@ ensures result == len(xs)
def f(xs: list[int]) -> int:
    return size(xs)
'''
ENUM = '''#@ ensures len(result) == len(xs)
def f(xs: list[int]) -> list[tuple[int,int,int]]:
    local = [(v, -v, i) for i, v in enumerate(xs)]
    local.sort()
    return local
'''

INTEGER = """#@ ensures result == (1 if n != 0 else 0)
def f(n: int) -> int:
    if n:
        return 1
    return 0
"""

@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
@pytest.mark.parametrize('source', [SORT, KEY, BISECT, OPTIONAL, READONLY, ENUM, INTEGER])
def test_sequence_translation_matches_python(tmp_path, source):
    p = tmp_path / 'sequence.py'; p.write_text(source)
    result = verify(p, tmp_path/'proof', time_limit=10)
    assert result['status'] == 'ok', result
    diff = difftest_file(p, tmp_path/'diff', examples=60)
    assert diff.ok, diff

@pytest.mark.parametrize('source', [
    SORT.replace('local = [v for v in xs]', 'local = xs'),
    SORT.replace('local.sort()', 'alias = local\n    local.sort()'),
    SORT.replace('local.sort()', 'local.sort(reverse=True)'),
    SORT.replace('local.sort()', 'for item in local:\n        local.sort()'),
    BISECT.replace('local = [v for v in xs]', 'local = xs'),
    BISECT.replace('del local[:cutoff]', 'del local[1:cutoff]'),
    BISECT.replace('insort(local, x)', 'insort(local, x, key=None)'),
    BISECT.replace('from bisect import bisect_right, insort', 'from bisect import bisect_right, insort\nfrom math import prod as insort'),
    BISECT.replace('from bisect import bisect_right, insort', 'from bisect import bisect_right, insort\nfrom math import *'),
    READONLY.replace('    return len(xs)', '    xs.append(1)\n    return len(xs)', 1),
    ENUM.replace('def f(xs:', 'def f(enumerate: int, xs:'),
    KEY.replace('(xs[i], *', '(True, *'),
    KEY.replace('xs[d] for d', 'True for d'),
    KEY.replace('key=lambda i', 'reverse=True, key=lambda i'),
    '#@ ensures True\ndef PyProd(xs: list[int]) -> int:\n    return 0\n',
])
def test_sequence_unsupported_semantics_fail_closed(source):
    with pytest.raises(EncodeError):
        encode(source)

NESTED = '''from bisect import bisect_right
#@ ensures result == all(all(v >= 0 for v in row) for row in xs)
def f(xs: list[list[int]]) -> bool:
    return all(all(v >= 0 for v in row) for row in xs)
'''

@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_nested_input_predicates_are_defined_checked_and_executed(tmp_path):
    encoded = encode(NESTED)
    assert 'ghost predicate VSpec' in encoded.dafny_source
    p = tmp_path / 'nested.py'; p.write_text(NESTED)
    result = verify(p, tmp_path/'proof', time_limit=10)
    assert result['status'] == 'ok', result
    assert difftest_file(p, tmp_path/'diff', examples=60).ok

@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_named_predicate_does_not_hide_undefined_indexing(tmp_path):
    source = '''from bisect import bisect_right
#@ ensures result == all(all(xs[a][b] >= 0 for b in range(2)) for a in range(len(xs)))
def f(xs: list[list[int]]) -> bool:
    return True
'''
    p = tmp_path/'partial.py'; p.write_text(source)
    result = verify(p, tmp_path/'proof', time_limit=10)
    assert result['status'] == 'failed', result
    assert any(f['kind'] in {'bounds', 'call-precondition'} for f in result['failures']), result

GHOST_LOOP = '''#@ requires n >= 0
#@ ensures result == n
def f(n: int) -> int:
    count = 0
    for i in range(n):
        #@ invariant ghost("Counted", count, i)
        count += 1
    return count
'''

@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_defined_ghost_predicate_checks_loop_without_entering_runtime(tmp_path):
    from veripy.backends.dafny.encoder import load_proof_sidecar
    from veripy.guards.emitter import emit_guarded
    p = tmp_path/'ghost_loop.py'; p.write_text(GHOST_LOOP)
    p.with_suffix('.proofs.dfy').write_text('predicate Counted(c: int, i: int) { c == i }\n')
    symbols = load_proof_sidecar(p).lemmas
    assert symbols == frozenset()
    assert symbols.predicates == frozenset({'Counted'})
    result = verify(p, tmp_path/'proof', time_limit=10)
    assert result['status'] == 'ok', result
    ns = {}; exec(emit_guarded(GHOST_LOOP, parse_source(GHOST_LOOP), p.name, check_ensures=True), ns)
    assert ns['f'](7) == 7

@pytest.mark.skipif(find_dafny() is None, reason='Dafny required')
def test_false_ghost_predicate_cannot_be_assumed(tmp_path):
    p = tmp_path/'bad_ghost.py'; p.write_text(GHOST_LOOP)
    p.with_suffix('.proofs.dfy').write_text('predicate Counted(c: int, i: int) { false }\n')
    result = verify(p, tmp_path/'proof', time_limit=10)
    assert result['status'] == 'failed', result
    assert any(f['kind'] == 'invariant' for f in result['failures'])

@pytest.mark.parametrize('body', [
    'predicate Counted(c: int, i: int)',
    'predicate Counted(c: int, i: int)\nlemma Later() {}',
    'predicate {:axiom} Counted(c: int, i: int)',
])
def test_ghost_predicates_still_require_checked_bodies(tmp_path, body):
    from veripy.backends.dafny.encoder import load_proof_sidecar
    p = tmp_path/'bad.py'; p.write_text(GHOST_LOOP)
    p.with_suffix('.proofs.dfy').write_text(body)
    with pytest.raises(EncodeError): load_proof_sidecar(p)

@pytest.mark.parametrize('kind', ['requires', 'ensures', 'decreases'])
def test_ghost_predicates_are_not_runtime_contracts(kind):
    source = f'#@ {kind} ghost("Counted", 0, 0)\n#@ ensures True\ndef f() -> int:\n    return 0\n'
    assert parse_source(source).errors
