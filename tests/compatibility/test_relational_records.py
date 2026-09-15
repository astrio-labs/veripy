"""Record product semantics: fields, nested sequences, outcomes, and rejection."""
from pathlib import Path
import json
import pytest
from veripy.compatibility import compare, _signature, _replay
from veripy.backends.dafny.driver import find_dafny

RECORD = 'from dataclasses import dataclass\n@dataclass(frozen=True)\nclass Point:\n    x: int\n'
HAS_DAFNY = pytest.mark.skipif(not find_dafny(), reason='Dafny required')


def run_pair(tmp_path, old, new, backend='dafny'):
    a, b = tmp_path/'old.py', tmp_path/'new.py'
    a.write_text(old); b.write_text(new)
    return compare(a, b, tmp_path/'run', time_limit=10, backend=backend)


@HAS_DAFNY
@pytest.mark.parametrize('delta', [0, 1])
def test_record_field_change_detected(tmp_path, delta):
    old = RECORD + '#@ ensures result == p.x\ndef f(p: Point) -> int:\n    return p.x\n'
    new = RECORD + f'#@ ensures result == p.x + {delta}\ndef f(p: Point) -> int:\n    return p.x + {delta}\n'
    result = run_pair(tmp_path, old, new)
    assert result['status'] == ('behavioral-difference' if delta else 'proved-compatible'), result
    assert result['replay'].get('admitted_samples', 0) > 0
    assert not result.get('proof_replay_contradiction', False)


@HAS_DAFNY
def test_nested_record_sequence_and_record_return(tmp_path):
    source = RECORD + '@dataclass(frozen=True)\nclass Box:\n    point: Point\n'
    source += '#@ requires len(xs) > 0\n#@ ensures result == xs[0].point\ndef f(xs: list[Box]) -> Point:\n    return xs[0].point\n'
    result = run_pair(tmp_path, source, source)
    assert result['status'] == 'proved-compatible', result
    assert result['replay']['admitted_samples'] > 0


@HAS_DAFNY
def test_record_list_field(tmp_path):
    source = RECORD.replace('x: int', 'x: list[int]')
    source += '#@ ensures result == p.x\ndef f(p: Point) -> list[int]:\n    return p.x\n'
    result = run_pair(tmp_path, source, source)
    assert result['status'] == 'proved-compatible', result


@HAS_DAFNY
def test_record_errors(tmp_path):
    source = RECORD + '#@ ensures raised() == (p.x < 0)\n#@ ensures raised() or result == p.x\ndef f(p: Point) -> int:\n    if p.x < 0:\n        raise ValueError("negative")\n    return p.x\n'
    result = run_pair(tmp_path, source, source, backend='dafny-outcomes')
    assert result['status'] == 'proved-compatible', result
    assert result['replay']['admitted_samples'] > 0


@HAS_DAFNY
def test_record_precondition_narrowing(tmp_path):
    source = RECORD + '#@ requires p.x >= 0\n#@ ensures result == p.x\ndef f(p: Point) -> int:\n    return p.x\n'
    result = run_pair(tmp_path, source, source.replace('p.x >= 0', 'p.x > 0'))
    assert result['status'] == 'behavioral-difference', result
    assert result['witness']['kind'] == 'precondition-narrowing'


@pytest.mark.parametrize('change', ['type', 'field'])
def test_different_schemas_rejected(tmp_path, change):
    source = RECORD + '#@ ensures True\ndef f(p: Point) -> int:\n    return 0\n'
    other = source.replace('x: int', 'x: bool' if change == 'type' else 'y: int')
    result = run_pair(tmp_path, source, other)
    assert result['status'] == 'unsupported'
    assert 'must match' in result['reason']


@pytest.mark.parametrize('body', ['p.x = 2\n    return p.x', 'return p is p'])
def test_mutation_identity_rejected(tmp_path, body):
    source = RECORD + '#@ ensures True\ndef f(p: Point) -> int:\n    ' + body + '\n'
    result = run_pair(tmp_path, source, source)
    assert result['status'] == 'unsupported', result


@pytest.mark.parametrize('body', ['p.x.append(1)\n    return 0', 'alias = p.x\n    alias.append(1)\n    return 0', 'p.x[0] = 1\n    return 0'])
def test_borrowed_list_mutation_rejected(tmp_path, body):
    source = RECORD.replace('x: int', 'x: list[int]')
    source += '#@ ensures True\ndef f(p: Point) -> int:\n    ' + body + '\n'
    result = run_pair(tmp_path, source, source)
    assert result['status'] == 'unsupported', result


def test_mutable_schema_rejected(tmp_path):
    source = RECORD.replace('frozen=True', 'frozen=False') + '#@ ensures True\ndef f(p: Point) -> int:\n    return 0\n'
    assert run_pair(tmp_path, source, source)['status'] == 'unsupported'


@HAS_DAFNY
def test_corrupt_field_bridge_is_exposed_by_native_replay(tmp_path, monkeypatch):
    import veripy.compatibility as compat
    bridge = compat._snapshot_bridges
    monkeypatch.setattr(compat, '_snapshot_bridges', lambda sig: bridge(sig).replace(
        'New.VMakePoint(value.vfieldx, value.vfieldy)', 'New.VMakePoint(value.vfieldy, value.vfieldx)'))
    schema = RECORD.replace('    x: int', '    x: int\n    y: int')
    old = schema + '#@ ensures result == p.x\ndef f(p: Point) -> int:\n    return p.x\n'
    new = old.replace('p.x', 'p.y')
    result = run_pair(tmp_path, old, new)
    assert result['status'] == 'behavioral-difference', result
    assert result['proof_replay_contradiction'] is True, result


@HAS_DAFNY
def test_tuple_of_record_sequences(tmp_path):
    source = RECORD + '#@ ensures result == (xs, 1)\ndef f(xs: list[Point]) -> tuple[list[Point], int]:\n    return (xs, 1)\n'
    result = run_pair(tmp_path, source, source)
    assert result['status'] == 'proved-compatible', result
