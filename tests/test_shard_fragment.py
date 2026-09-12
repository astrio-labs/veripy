"""Semantic boundaries needed by the PyTorch shard case study."""
from pathlib import Path
import math
import pytest
from veripy.frontend.extract import parse_source
from veripy.backends.dafny.encoder import encode_module, EncodeError
from veripy.backends.dafny.outcomes import encode_outcomes
from veripy.guards.emitter import emit_guarded
from veripy.guards.outcomes import emit_outcome_guarded
from veripy.guards.runtime import TypeGuardError, PostconditionError

HERE = Path(__file__).resolve().parents[1] / 'case_studies/repository_driven_v2/pytorch-shards'
PAIR = (HERE / 'pair.py').read_text()
TENSOR = (HERE / 'tensor.py').read_text()


def module(source, outcomes=False):
    ns = {}
    emitter = emit_outcome_guarded if outcomes else emit_guarded
    # Proof comments are checked against sidecar lemma names by the verifier;
    # guard encoding needs the same names but does not execute ghost calls.
    if outcomes:
        source = '\n'.join(l for l in source.splitlines() if '#@ proof' not in l)
    exec(emitter(source, parse_source(source), 'shard.py', check_ensures=True), ns)
    return ns


def test_pair_zero_size_is_exact_upstream_policy():
    ns = module(PAIR); cls = ns['ShardMetadata']; f = ns['_check_shard_metadata_pair_overlap']
    assert f(cls([2], [0]), cls([0], [5])) is True
    assert f(cls([], []), cls([], [])) is True
    assert f(cls([5], [2]), cls([0], [5])) is False


@pytest.mark.parametrize('statement', ['shard1.shard_sizes[0] = 99',
    'xs = shard1.shard_sizes\n    xs.append(99)', 'shard1.shard_sizes.clear()',
    'del shard1.shard_offsets[:]', 'shard1.shard_offsets = []'])
def test_list_record_mutation_fails_closed(statement):
    source = PAIR.replace('    ndims = ', '    ' + statement + '\n    ndims = ')
    with pytest.raises(EncodeError):
        encode_module(source, parse_source(source), "test.py")


@pytest.mark.parametrize('value', [[True], [1.0]])
def test_nested_exact_types(value):
    ns = module(PAIR); cls = ns['ShardMetadata']
    with pytest.raises(TypeGuardError):
        ns['_check_shard_metadata_pair_overlap'](cls(value, [1]), cls([0], [1]))


@pytest.mark.parametrize('shards,dims,error', [([([0], [3])], [3], False),
    ([([0], [3])], [2], True), ([([0], [2])], [3], True),
    ([([], [])], [], False), ([([0], [0])], [0], False),
    ([([0], [1])], [], True)])
def test_none_outcomes(shards, dims, error):
    ns = module(TENSOR, True); values = [ns['ShardMetadata'](*s) for s in shards]
    if error:
        with pytest.raises(ValueError): ns['check_tensor'](values, dims)
    else:
        assert ns['check_tensor'](values, dims) is None


def test_outcome_guard_detects_wrong_error_policy():
    source = TENSOR.replace('if total_shard_volume != tensor_volume:', 'if total_shard_volume == tensor_volume:')
    ns = module(source, True)
    with pytest.raises(PostconditionError):
        ns['check_tensor']([ns['ShardMetadata']([0], [3])], [3])


def test_none_result_not_exposed_as_boolean():
    source = TENSOR.replace('#@ ensures raised()', '#@ ensures result == False\n#@ ensures raised()')
    with pytest.raises(EncodeError, match='result is not exposed'):
        encode_outcomes(source, parse_source(source), proof_lemmas={"ProductStep", "FullProduct", "SumExtension"})


@pytest.mark.parametrize('expr', ['prod(xs, start=2)', 'prod(2)', 'prod(xs, 2)'])
def test_product_unsupported_arguments(expr):
    source = f'from math import prod\n#@ ensures True\ndef f(xs: list[int]) -> int:\n    return {expr}\n'
    with pytest.raises(EncodeError): encode_module(source, parse_source(source), "test.py")
