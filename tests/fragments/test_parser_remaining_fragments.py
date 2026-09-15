"""Semantic controls for the source-preserving CPython parser extensions."""
import ast

import pytest

from veripy.api import verify
from veripy.frontend.extract import parse_source
from veripy.frontend.fixed_loops import lower_fixed_loops
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.driver import verify_lean_file

MULTIPLY = '''FACTORS = [2, 3]
#@ ensures result == x * 3
def multiply(x: int) -> int:
    values = [x]
    index = -1
    values[index] *= FACTORS[-1]
    return values[0]
'''
MAP = '''#@ ensures result == (c in "012")
def digit(c: str) -> bool:
    return c in "012"
#@ ensures result == all(c in "012" for c in s)
def all_digits(s: str) -> bool:
    return all(map(digit, s))
#@ ensures result == any(c in "012" for c in s)
def any_digits(s: str) -> bool:
    return any(map(digit, s))
'''
LOOP = '''#@ ensures result == (0 if stop <= 1 else 1 if stop == 2 else 3)
def count(stop: int) -> int:
    total = 0
    for i in range(3):
        if i >= stop:
            break
        total += i
    return total
'''

@pytest.mark.parametrize('backend', ['dafny-outcomes', 'lean'])
@pytest.mark.parametrize('source', [MULTIPLY, MAP, LOOP])
@pytest.mark.requires_prover()
def test_contracts(tmp_path, backend, source):
    path = tmp_path/'control.py'; path.write_text(source)
    result = verify(path, tmp_path/'proof', backend=backend, time_limit=120, keep_artifacts=True)
    assert result['status'] == 'ok', str(result.get('failures'))[:1800]

@pytest.mark.parametrize('body', [
    '    alias = values\n    values[0] *= 2\n    return alias[0]',
    '    values[0] *= int("2")\n    return values[0]',
])
def test_unsupported_multiplication_rejected(body):
    source = '#@ ensures result == 2\ndef f() -> int:\n    values = [1]\n'+body+'\n'
    with pytest.raises(EncodeError):
        encode_outcomes(source, parse_source(source), 'bad.py')

@pytest.mark.parametrize('change', [
    lambda s: s.replace('return c in "012"', 'return c[0] in "012"'),
    lambda s: s.replace('def digit', '#@ requires len(c) == 1\ndef digit'),
    lambda s: s.replace('map(digit, s)', 'map(digit, s, s)'),
])
def test_non_total_or_other_maps_rejected(change):
    source = change(MAP)
    with pytest.raises(EncodeError):
        encode_outcomes(source, parse_source(source), 'bad.py')


def test_fixed_loop_native_equivalence_and_break_scope():
    # Deliberately collide with the first synthesized flag, and retain the
    # final loop target, nested breaks, and statements following a break.
    source = '''#@ ensures result == result
def f(stop: int) -> int:
    __vp_fixed_active_5 = 7
    total = 0
    for i in range(1, 5):
        if i >= stop:
            if i % 2 == 0:
                break
            total += 10
        total += i
    return total * 100 + i + __vp_fixed_active_5
'''
    original = {}; exec(source, original)
    tree = lower_fixed_loops(ast.parse(source), parse_source(source))
    assert not any(isinstance(n, ast.For) for n in ast.walk(tree))
    lowered = {}; exec(compile(tree, 'lowered.py', 'exec'), lowered)
    for stop in range(-2, 8):
        assert lowered['f'](stop) == original['f'](stop)


@pytest.mark.parametrize('body', ['continue', 'return i', 'i += 1', 'for j in range(2):\n            pass'])
def test_fixed_loop_unsupported_shapes_unchanged(body):
    source = '#@ ensures result == 0\ndef f() -> int:\n    for i in range(3):\n        '+body+'\n    return 0\n'
    tree = ast.parse(source)
    assert ast.dump(lower_fixed_loops(tree, parse_source(source))) == ast.dump(tree)


@pytest.mark.requires_prover('lean')
def test_kernel_replays_and_augassign_error_order(tmp_path):
    error_source = '''#@ requires -1 <= i < 1 and d != 0
#@ ensures result == 6 * (8 // d)
def order(i: int, d: int) -> int:
    xs = [6]
    xs[i] *= 8 // d
    return xs[0]
'''
    source = MULTIPLY + MAP + LOOP + error_source
    namespace = {}; exec(source, namespace)
    encoded = encode_imperative(source, parse_source(source), 'replay.py').lean_source
    model = encoded.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    commands = []
    def check(call, expected):
        commands.append(f'theorem replay_{len(commands)} : {call} = {expected} := by native_decide')
    for n in [-4, 0, 9]: check(f'multiply ({n})', f'Except.ok ({namespace["multiply"](n)})')
    for s in ['', '012', '201', '01x', '１２', '🙂']:
        literal = '['+','.join(str(ord(c)) for c in s)+']'
        for name in ['all_digits', 'any_digits']:
            check(f'{name} {literal}', 'Except.ok '+str(namespace[name](s)).lower())
    for stop in range(-1, 5): check(f'count ({stop})', f'Except.ok ({namespace["count"](stop)})')
    for i, d in [(2, 0), (0, 0), (-1, 2), (0, -3)]:
        try: expected = f'Except.ok ({namespace["order"](i, d)})'
        except IndexError: expected = 'Except.error VeriPy.Error.index'
        except ZeroDivisionError: expected = 'Except.error VeriPy.Error.zero'
        check(f'order ({i}) ({d})', expected)
    # rfl forces kernel reduction, avoiding native_decide trust in controls.
    path = tmp_path/'replay.lean'
    path.write_text(model+'\n'+'\n'.join(commands).replace('by native_decide', 'by rfl'))
    result = verify_lean_file(path, {}, time_limit=120, stub_extent=None)
    assert result.ok, result.raw[-2500:]

@pytest.mark.parametrize('name', ['range', 'map'])
def test_intrinsics_cannot_be_shadowed(name):
    source = LOOP.replace('stop: int', 'stop: int, '+name+': int') if name == 'range' else MAP.replace('s: str', 's: str, map: int')
    with pytest.raises(EncodeError):
        encode_outcomes(source, parse_source(source), 'shadow.py')


@pytest.mark.requires_prover('dafny', 'lean')
def test_fixed_loop_guard_optimization_preserves_partial_short_circuit(tmp_path):
    source = '''#@ ensures result == (0 if flag or not text else 2)
def total_guard(flag: bool, text: str) -> int:
    count = 0
    for i in range(2):
        if flag or not text:
            break
        count += 1
    return count
#@ requires flag or divisor != 0
#@ ensures result >= 0
def partial_guard(flag: bool, divisor: int) -> int:
    count = 0
    for i in range(2):
        if flag or 10 // divisor > 0:
            break
        count += 1
    return count
'''
    encoded = encode_imperative(source, parse_source(source), 'guards.py').lean_source
    total = encoded.split('def «total_guard»')[1].split('def «total_guard__error»')[0]
    partial = encoded.split('def «partial_guard»')[1].split('def «partial_guard__error»')[0]
    assert '∨' in total and '(← (do if' not in total
    assert '(← (do if' in partial
    model = encoded.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    model += '''
theorem guarded_zero : partial_guard true 0 = Except.ok 0 := by rfl
theorem evaluated_zero : partial_guard false 0 = Except.error VeriPy.Error.zero := by rfl
theorem positive : partial_guard false 2 = Except.ok 0 := by rfl
theorem negative : partial_guard false (-2) = Except.ok 2 := by rfl
theorem total_empty : total_guard false [] = Except.ok 0 := by rfl
theorem total_nonempty : total_guard false [65] = Except.ok 2 := by rfl
'''
    path = tmp_path/'guards.lean'; path.write_text(model)
    result = verify_lean_file(path, {}, time_limit=120, stub_extent=None)
    assert result.ok, result.raw[-2000:]

PEELED = '''#@ ensures result >= 0
def initialize_once(n: int) -> int:
    count = 0
    for i in range(3):
        #@ invariant count >= 0
        if i == 0:
            positive = n > 0
        if positive and i == 1:
            break
        count += 1
    return count
'''

@pytest.mark.parametrize('backend', ['dafny-outcomes', 'lean'])
@pytest.mark.requires_prover()
def test_annotated_first_iteration_initialization(tmp_path, backend):
    path = tmp_path/'peel.py'; path.write_text(PEELED)
    result = verify(path, tmp_path/'proof', backend=backend, time_limit=120, keep_artifacts=True)
    assert result['status'] == 'ok', str(result.get('failures'))[:1800]


def test_peeling_preserves_break_and_skips_escaping_target():
    tree = lower_fixed_loops(ast.parse(PEELED), parse_source(PEELED))
    loops = [n for n in ast.walk(tree) if isinstance(n, ast.For)]
    assert len(loops) == 1 and ast.unparse(loops[0].iter) == 'range(1, 3)'
    original = {}; lowered = {}; exec(PEELED, original)
    exec(compile(tree, 'peeled.py', 'exec'), lowered)
    for n in range(-3, 4):
        assert original['initialize_once'](n) == lowered['initialize_once'](n)
    escaping = PEELED.replace('return count', 'return i')
    assert ast.dump(lower_fixed_loops(ast.parse(escaping), parse_source(escaping))) == ast.dump(ast.parse(escaping))

@pytest.mark.parametrize('backend', ['dafny-outcomes', 'lean'])
@pytest.mark.requires_prover()
def test_peeled_loop_rejects_broken_invariant(tmp_path, backend):
    source = PEELED.replace('count += 1', 'count -= 1')
    path = tmp_path/'negative.py'; path.write_text(source)
    result = verify(path, tmp_path/'proof', backend=backend, time_limit=120, keep_artifacts=True)
    assert result['status'] == 'failed', result
    assert not any(f['kind'] in ('timeout', 'resolution') for f in result.get('failures', [])), result
