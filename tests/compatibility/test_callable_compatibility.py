"""Callable ghost contracts and checked backward-compatibility products."""
from pathlib import Path
import pytest
from veripy.api import verify
from veripy.backends.dafny.encoder import encode_module, load_proof_sidecar, EncodeError
from veripy.backends.dafny.driver import find_dafny
from veripy.backends.lean.encoder import encode_module_lean
from veripy.frontend.extract import parse_source
from veripy.guards.emitter import emit_guarded
from veripy.compatibility import compare

HAS_DAFNY = pytest.mark.skipif(not find_dafny(), reason='Dafny required')
CONTRACT = '''#@ ghost_ensures ghost("Exact", xs, result)
def helper(xs: list[int]) -> list[int]:
    return xs

#@ ghost_ensures ghost("Exact", xs, result)
def caller(xs: list[int]) -> list[int]:
    result_list = helper(xs)
    return result_list
'''
PREDICATE = 'predicate Exact(xs: seq<int>, output: seq<int>) { output == xs }\n'


def source_file(tmp_path, text=CONTRACT, proof=PREDICATE):
    path = tmp_path / 'sample.py'
    path.write_text(text)
    path.with_suffix('.proofs.dfy').write_text(proof)
    return path


@HAS_DAFNY
@pytest.mark.parametrize('mutation', ['', 'return result_list|return []', 'return xs|return []'])
def test_contract_is_checked_at_actual_return(tmp_path, mutation):
    source = CONTRACT
    if mutation:
        source = source.replace(*mutation.split('|'))
    path = source_file(tmp_path, source)
    result = verify(path, tmp_path/'proof', keep_artifacts=True)
    assert result['status'] == ('failed' if mutation else 'ok'), result


@pytest.mark.parametrize('mutation', ['result_list.append(1)', 'xs.append(1)'])
def test_sequence_result_remains_readonly(tmp_path, mutation):
    source = CONTRACT.replace('    return result_list', '    '+mutation+'\n    return result_list')
    path = source_file(tmp_path, source)
    with pytest.raises(EncodeError, match='fresh|unaliased'):
        encode_module(source, parse_source(source), path.name, load_proof_sidecar(path).lemmas)


def test_sequence_call_invalidates_owned_alias(tmp_path):
    source = CONTRACT.replace('    result_list = helper(xs)', '    owned = [1]\n    result_list = helper(owned)\n    owned.append(2)')
    path = source_file(tmp_path, source)
    with pytest.raises(EncodeError, match='fresh|unaliased'):
        encode_module(source, parse_source(source), path.name, load_proof_sidecar(path).lemmas)


def test_ghost_contract_requires_defined_predicate(tmp_path):
    path = source_file(tmp_path, proof='lemma Exact(xs: seq<int>, output: seq<int>) {}\n')
    with pytest.raises(EncodeError):
        encode_module(CONTRACT, parse_source(CONTRACT), path.name, load_proof_sidecar(path).lemmas)


@pytest.mark.parametrize('source', [CONTRACT.replace('ghost_ensures','ensures'), '#@ ensures True\ndef f(x: int) -> int:\n    #@ ghost_ensures result == x\n    return x\n'])
def test_ghost_clause_placement_and_ordinary_ensures(source):
    specs = parse_source(source)
    assert specs.errors or specs.orphans


def test_runtime_guard_retains_normal_contract_without_evaluating_ghost(tmp_path):
    path = source_file(tmp_path)
    source = CONTRACT.replace('#@ ghost_ensures', '#@ ensures len(result) == len(xs)\n#@ ghost_ensures')
    ns = {}
    exec(emit_guarded(source, parse_source(source), path.name, check_ensures=True), ns)
    assert ns['caller']([3,1]) == [3,1]


def test_lean_does_not_ignore_ghost_contract():
    with pytest.raises(EncodeError, match='ghost_ensures'):
        encode_module_lean(CONTRACT, parse_source(CONTRACT), 'sample.py')


@HAS_DAFNY
@pytest.mark.parametrize('old_pre,new_pre,new_expr,status,kind', [
    ('x >= 0','x >= -1','x + 1','proved-compatible',None),
    ('x >= 0','x > 0','x + 1','behavioral-difference','precondition-narrowing'),
    ('True','True','x + 2','behavioral-difference','observable-difference'),
])
def test_general_product(tmp_path, old_pre, new_pre, new_expr, status, kind):
    old = f'#@ requires {old_pre}\n#@ ensures result == x + 1\ndef f(x: int) -> int:\n    return x + 1\n'
    new = f'#@ requires {new_pre}\n#@ ensures result == {new_expr}\ndef renamed(x: int) -> int:\n    return {new_expr}\n'
    a=tmp_path/'a.py'; b=tmp_path/'b.py'; a.write_text(old); b.write_text(new)
    result=compare(a,b,tmp_path/'out',new_function='renamed',time_limit=5)
    assert result['status']==status, result
    if kind: assert result['witness']['kind']==kind


@HAS_DAFNY
def test_weak_contracts_are_inconclusive(tmp_path):
    source='#@ ensures True\ndef f(x: int) -> int:\n    return x + 1\n'
    a=source_file(tmp_path,source,proof='')
    result=compare(a,a,tmp_path/'out',time_limit=5)
    assert result['status']=='inconclusive', result


@HAS_DAFNY
@pytest.mark.parametrize('change', [False,True])
def test_valueerror_outcome_product(tmp_path, change):
    source='#@ ensures raised() <==> x < 0\n#@ ensures not raised() ==> result == x\ndef f(x: int) -> int:\n    if x < 0:\n        raise ValueError("negative")\n    return x\n'
    a=tmp_path/'a.py'; b=tmp_path/'b.py'; a.write_text(source)
    b.write_text(source if not change else '#@ ensures not raised() and result == x\ndef f(x: int) -> int:\n    return x\n')
    result=compare(a,b,tmp_path/'out',backend='dafny-outcomes',time_limit=5)
    assert result['status']==('behavioral-difference' if change else 'proved-compatible'),result


@pytest.mark.parametrize('source', [
    '#@ ensures True\ndef f(x: float) -> float:\n    return x\n',
    '#@ ensures True\ndef f(x: int) -> int:\n    raise TypeError("x")\n',
])
def test_unsupported_is_not_difference(tmp_path, source):
    a=source_file(tmp_path,source,proof='')
    assert compare(a,a,tmp_path/'out',backend='dafny-outcomes')['status']=='unsupported'


@HAS_DAFNY
@pytest.mark.parametrize('proof', [
    'lemma CompatibilityRelation(x: int) ensures false {}\n',
    'lemma CompatibilityRelation(x: int) requires x > 100 ensures true {}\n',
])
def test_relational_hints_are_proved_and_preconditions_checked(tmp_path, proof):
    source='#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n'
    a=source_file(tmp_path,source,proof='')
    relation=tmp_path/'relation.dfy';relation.write_text(proof)
    result=compare(a,a,tmp_path/'out',relation=relation,time_limit=5)
    assert result['status']=='inconclusive',result


def test_relational_axioms_are_rejected(tmp_path):
    source='#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n'
    a=source_file(tmp_path,source,proof='')
    relation=tmp_path/'relation.dfy';relation.write_text('lemma {:axiom} CompatibilityRelation(x: int) ensures false\n')
    assert compare(a,a,tmp_path/'out',relation=relation)['status']=='unsupported'


@HAS_DAFNY
@pytest.mark.parametrize('typ,expr', [('list[int]','xs'),('tuple[int,int]','(xs[0], xs[1])')])
def test_value_sequence_and_tuple_boundaries(tmp_path,typ,expr):
    source=f'#@ ensures result == xs\ndef f(xs: {typ}) -> {typ}:\n    return {expr}\n'
    a=source_file(tmp_path,source,proof='')
    result=compare(a,a,tmp_path/'out',time_limit=5)
    assert result['status']=='proved-compatible',result


@pytest.mark.parametrize('suffix', ['\nf = lambda x: 0\n','\nfrom external import f\n'])
def test_top_level_replacement_cannot_be_certified(tmp_path,suffix):
    a=source_file(tmp_path,'#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n'+suffix,proof='')
    assert compare(a,a,tmp_path/'out')['status']=='unsupported'


@HAS_DAFNY
@pytest.mark.parametrize('parameter', ['oldResult','newResult','oldError','newError'])
def test_product_locals_never_shadow_arguments(tmp_path,parameter):
    a=tmp_path/'a.py';b=tmp_path/'b.py'
    # If oldResult shadows the input, the second call sees the first result
    # (always zero) and can incorrectly appear equal. Sample beyond replay's
    # pool so only the sound product distinguishes this from a proof.
    a.write_text(f'#@ ensures result == 0\ndef f({parameter}: int) -> int:\n    return 0\n')
    b.write_text(f'#@ ensures result == (1 if {parameter} == 424242 else 0)\ndef f({parameter}: int) -> int:\n    return 1 if {parameter} == 424242 else 0\n')
    result=compare(a,b,tmp_path/'out',time_limit=5)
    assert result['status']=='inconclusive',result
    artifact=(tmp_path/'out/comparison.dfy').read_text()
    assert f'var {parameter}_' in artifact


@pytest.mark.parametrize('parameter',['Old','New','CompatibilityRelation'])
def test_comparison_namespace_collisions_are_explicit(tmp_path,parameter):
    a=source_file(tmp_path,f'#@ ensures result == {parameter}\ndef f({parameter}: int) -> int:\n    return {parameter}\n',proof='')
    result=compare(a,a,tmp_path/'out')
    assert result['status']=='unsupported',result


@HAS_DAFNY
def test_relation_cannot_smuggle_input_assumptions(tmp_path):
    source = '#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n'
    old = tmp_path/'old.py'; new = tmp_path/'new.py'
    old.write_text(source); new.write_text(source)
    relation = tmp_path/'relation.dfy'
    relation.write_text('lemma CompatibilityRelation(x: int) requires x > 0 {}\n')
    result = compare(old,new,tmp_path/'checked',relation=relation)
    assert result['status'] == 'inconclusive', result
    assert not result['proof']['ok']
