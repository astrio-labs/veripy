"""Sound admission and actual Lean checking for the imperative extension."""
from pathlib import Path
import pytest
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.backend import LeanBackend
from veripy.backends.lean.driver import find_lean
from veripy.frontend.extract import parse_source

RECORD='''from dataclasses import dataclass
@dataclass(frozen=True)
class Box:
    value: int
#@ ensures result == x.value + 1
def bump(x: Box) -> int:
    return x.value + 1
'''

def test_record_model_preserves_typed_program_and_contract():
    e=encode_imperative(RECORD,parse_source(RECORD),'box.py')
    assert 'structure «Box»' in e.lean_source
    assert 'Except VeriPy.Error Int' in e.lean_source
    assert 'def «bump__post»' in e.lean_source
    assert '#print axioms «bump_spec»' in e.lean_source

@pytest.mark.parametrize('source',[
 RECORD.replace('x.value + 1\n','x.value + 1.5\n'),
 RECORD.replace('from dataclasses import dataclass','from dataclasses import dataclass\nlen = 1'),
 RECORD.replace('x: Box','__vp_result: Box').replace('x.value','__vp_result.value'),
])
def test_unsafe_or_unimplemented_translation_rejected(source):
    with pytest.raises(EncodeError):encode_imperative(source,parse_source(source),'bad.py')

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_record_proof_and_false_contract(tmp_path):
    from veripy.api import verify
    p=tmp_path/'box.py';p.write_text(RECORD)
    ok=verify(p,tmp_path/'good',backend='lean',time_limit=120,keep_artifacts=True)
    assert ok['status']=='ok',ok
    p.write_text(RECORD.replace('ensures result == x.value + 1','ensures result == x.value + 2'))
    bad=verify(p,tmp_path/'bad',backend='lean',time_limit=120,keep_artifacts=True)
    assert bad['status']=='failed',bad
    assert any(f['kind']=='postcondition' for f in bad['failures']),bad


def test_sidecar_insertion_moves_source_coordinates():
    from types import SimpleNamespace
    backend=LeanBackend()
    e=encode_imperative(RECORD,parse_source(RECORD),'box.py')
    original=dict(e.line_map)
    marker_line=e.lean_source[:e.lean_source.index('-- VERIPY IMPERATIVE PROOF SUPPORT')].count('\n')+1
    sidecar=SimpleNamespace(text='theorem extra : True := by trivial\n')
    full=backend.compose_artifact(e,sidecar)
    assert e.sidecar_ranges==[(marker_line+1,marker_line+2)]
    assert all(e.line_map[line+2 if line>marker_line else line]==py for line,py in original.items())
    assert e.artifact_extent==full.count('\n')+1
    assert backend.compose_artifact(e,sidecar)==full


@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_negative_indexing_has_python_value_and_error_semantics(tmp_path):
    from veripy.backends.lean.driver import verify_lean_file
    source = """#@ requires len(xs) > 0
#@ ensures result == xs[-1]
def last(xs: list[int]) -> int:
    return xs[-1]
"""
    e=encode_imperative(source,parse_source(source),'last.py')
    model=e.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    # Both normal and error outcomes are checked by kernel reduction.
    code=model+"""
theorem last_value : last [4, 9] = Except.ok 9 := by rfl
theorem last_error : last [] = Except.error VeriPy.Error.index := by rfl
#print axioms last_value
#print axioms last_error
"""
    path=tmp_path/'negative.lean';path.write_text(code)
    result=verify_lean_file(path,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw


def test_split_sidecar_tracks_both_insertions():
    from types import SimpleNamespace
    backend=LeanBackend();e=encode_imperative(RECORD,parse_source(RECORD),'box.py')
    original=dict(e.line_map)
    sidecar=SimpleNamespace(text='def support : Nat := 1\n-- VERIPY PRELUDE END\ntheorem extra : support = 1 := by rfl\n')
    artifact=backend.compose_artifact(e,sidecar)
    assert artifact.index('structure «Box»') < artifact.index('def support') < artifact.index('def «bump»')
    assert artifact.index('theorem extra') > artifact.index('def «bump__post»')
    assert len(e.sidecar_ranges)==2
    assert backend.compose_artifact(e,sidecar)==artifact
    assert len(e.line_map)==len(original)

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_composed_helper_contracts_and_branch_values(tmp_path):
    from veripy.api import verify
    source='''#@ ensures result == x + 1
def increment(x: int) -> int:
    return x + 1

#@ ensures result >= 1
def magnitude_plus_one(x: int) -> int:
    if x >= 0:
        magnitude = x
    else:
        magnitude = -x
    return increment(magnitude)
'''
    p=tmp_path/'helpers.py';p.write_text(source)
    report=verify(p,tmp_path/'proof',backend='lean',time_limit=120,keep_artifacts=True)
    assert report['status']=='ok',report
    p.write_text(source.replace('return increment(magnitude)','return increment(magnitude) - 2'))
    bad=verify(p,tmp_path/'bad',backend='lean',time_limit=120,keep_artifacts=True)
    assert bad['status']=='failed',bad

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_distinct_invariants_for_loops_with_identical_state_types(tmp_path):
    from veripy.api import verify
    source='''#@ ensures result == len(xs) + 2 * len(ys)
def weighted_lengths(xs: list[int], ys: list[int]) -> int:
    first = 0
    for x in xs:
        #@ invariant first == loop_index()
        first += 1
    second = 0
    for y in ys:
        #@ invariant second == 2 * loop_index()
        second += 2
    return first + second
'''
    p=tmp_path/'loops.py';p.write_text(source)
    report=verify(p,tmp_path/'good',backend='lean',time_limit=120,keep_artifacts=True)
    assert report['status']=='ok',report
    p.write_text(source.replace('second += 2','second += 3'))
    bad=verify(p,tmp_path/'bad',backend='lean',time_limit=120,keep_artifacts=True)
    assert bad['status']=='failed',bad

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_binary_insertion_and_lexicographic_primitives(tmp_path):
    from veripy.backends.lean.imperative import PRELUDE
    from veripy.backends.lean.driver import verify_lean_file
    # Unsorted inputs matter: bisect's binary-search behavior differs from
    # counting values <= the key. These cases pin the actual Python operation.
    import bisect,itertools
    checks=[]
    cases=[([],0),([2,1,3],1),([3,1,2],2),([1,1,1],1),([-2,0,4],-3),([-2,0,4],8)]
    for i,(xs,x) in enumerate(cases):
        expected=bisect.bisect_right(xs,x);inserted=xs.copy();bisect.insort(inserted,x)
        checks.append(f'theorem bisect_{i} : VeriPy.bisectRight (fun a b : Int => decide (a≤b)) {xs} ({x}) = {expected} := by rfl')
        checks.append(f'theorem insert_{i} : VeriPy.insort (fun a b : Int => decide (a≤b)) {xs} ({x}) = {inserted} := by rfl')
    for i,(a,b) in enumerate(itertools.product([[],[0],[0,0],[0,1],[-1,3]],repeat=2)):
        checks.append(f'theorem lex_{i} : VeriPy.lexInts {a} {b} = {str(a<=b).lower()} := by rfl')
    path=tmp_path/'primitives.lean';path.write_text(PRELUDE+'\n'.join(checks))
    result=verify_lean_file(path,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_branch_duplicated_nested_loop_invariants(tmp_path):
    from veripy.api import verify
    source='''#@ ensures result == len(xs)
def nested(xs: list[int], ys: list[int]) -> int:
    total = 0
    for x in xs:
        #@ invariant total == loop_index()
        if x < 0:
            offset = 0
        else:
            offset = 1
        inner = 0
        for y in ys:
            #@ invariant inner == 2 * loop_index()
            inner += 2
        total += 1
    return total
'''
    path=tmp_path/'nested.py';path.write_text(source)
    good=verify(path,tmp_path/'good',backend='lean',time_limit=120,keep_artifacts=True)
    assert good['status']=='ok',good
    path.write_text(source.replace('inner += 2','inner += 3'))
    bad=verify(path,tmp_path/'bad',backend='lean',time_limit=120,keep_artifacts=True)
    assert bad['status']=='failed',bad

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_record_constructor_preserves_keyword_evaluation_order(tmp_path):
    from veripy.backends.lean.driver import verify_lean_file
    source='''from dataclasses import dataclass
@dataclass(frozen=True)
class Pair:
    first: int
    second: int
#@ ensures result.first == 1
#@ ensures result.second == 2
def construct() -> Pair:
    return Pair(second=2, first=1)
#@ requires len(xs) > 0
#@ ensures result.first == xs[0]
def bad(xs: list[int]) -> Pair:
    return Pair(second=1 // 0, first=xs[0])
'''
    encoded=encode_imperative(source,parse_source(source),'construction.py')
    model=encoded.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    model+='''
theorem construction : construct = Except.ok (Pair.mk 1 2) := by rfl
theorem argument_order : bad [] = Except.error VeriPy.Error.zero := by rfl
#print axioms construction
#print axioms argument_order
'''
    path=tmp_path/'construction.lean';path.write_text(model)
    result=verify_lean_file(path,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_cursor_capture_resolves_append_notation(tmp_path):
    from veripy.backends.lean.imperative import PRELUDE
    from veripy.backends.lean.driver import verify_lean_file
    # mvcgen uses overloaded ++ in its cursor equality. Selecting another Int
    # from context can silently produce the wrong invariant template.
    source=PRELUDE+'''
theorem capture_cursor (xs pref suff : List Int) (current unrelated : Int)
    (h : VeriPy.loopTag 71 xs = pref ++ current :: suff) : current = current := by
  veripy_cursor idx 71 0 0 0
  change idx = current
  rfl
#print axioms capture_cursor
'''
    p=tmp_path/'cursor.lean';p.write_text(source)
    result=verify_lean_file(p,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_checked_quantifiers_and_exception_argument_order(tmp_path):
    from veripy.backends.lean.driver import verify_lean_file
    source='''#@ ensures True
def every(xs: list[list[int]]) -> bool:
    return all(row[0] > 0 for row in xs)
#@ ensures True
def any_positive(xs: list[list[int]]) -> bool:
    return any(row[0] > 0 for row in xs)
#@ ensures True
def reject(xs: list[int]) -> None:
    raise ValueError(f"Bad value {xs[0]}")
#@ ensures True
def reject_list(xs: list[int]) -> None:
    raise ValueError(f"Bad values {list(xs)!r}")
'''
    e=encode_imperative(source,parse_source(source),'checked.py')
    model=e.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    proof=model+'''
theorem all_short : every [[0], []] = Except.ok false := by rfl
theorem all_failure : every [[1], []] = Except.error VeriPy.Error.index := by rfl
theorem all_empty : every [] = Except.ok true := by rfl
theorem any_short : any_positive [[1], []] = Except.ok true := by rfl
theorem any_failure : any_positive [[0], []] = Except.error VeriPy.Error.index := by rfl
theorem any_empty : any_positive [] = Except.ok false := by rfl
theorem argument_failure : reject [] = Except.error VeriPy.Error.index := by rfl
theorem raised_value : reject [4] = Except.error VeriPy.Error.value := by rfl
theorem list_message : reject_list [1,2] = Except.error VeriPy.Error.value := by rfl
'''
    p=tmp_path/'checked.lean';p.write_text(proof)
    result=verify_lean_file(p,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_checked_whole_function_sidecar_proof(tmp_path):
    from veripy.api import verify
    e=encode_imperative(RECORD,parse_source(RECORD),'box.py')
    support=e.lean_source.split('@[spec] theorem «bump_spec»')[1]
    support='theorem bump__proof'+support.split('#print axioms')[0]
    p=tmp_path/'box.py';p.write_text(RECORD)
    sidecar=tmp_path/'box.proofs.lean';sidecar.write_text(support)
    good=verify(p,tmp_path/'good',backend='lean',time_limit=120,keep_artifacts=True)
    assert good['status']=='ok',good
    # A true theorem with the wrong type cannot discharge the generated triple.
    sidecar.write_text('theorem bump__proof (x : Box) : True := by trivial\n')
    bad=verify(p,tmp_path/'bad',backend='lean',time_limit=120,keep_artifacts=True)
    assert bad['status']=='failed',bad

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_break_exits_only_innermost_loop(tmp_path):
    from veripy.backends.lean.driver import verify_lean_file
    source='''#@ ensures result >= 0
def count_rows(xs: list[list[int]]) -> int:
    count = 0
    for row in xs:
        #@ invariant count >= 0
        for item in row:
            #@ invariant count >= 0
            if item == 0:
                break
            count += 1
    return count
'''
    e=encode_imperative(source,parse_source(source),'breaks.py')
    model=e.lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    p=tmp_path/'breaks.lean';p.write_text(model+'''
theorem nested_break : count_rows [[1,0,2],[3,4],[0,5]] = Except.ok 3 := by rfl
theorem empty_break : count_rows [] = Except.ok 0 := by rfl
''')
    result=verify_lean_file(p,{},time_limit=120,stub_extent=None)
    assert result.ok,result.raw

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_sorted_iterable_is_one_tagged_argument(tmp_path):
    from veripy.api import verify
    source='''#@ ensures result == len(xs)
def sorted_length(xs: list[int]) -> int:
    total = 0
    for item in sorted(xs):
        #@ invariant total == loop_index()
        total += 1
    return total
'''
    p=tmp_path/'sorted_loop.py';p.write_text(source)
    # This automation-heavy proof exceeded 120s under background load.
    # Keep an explicit finite budget now that the driver enforces real seconds.
    good=verify(p,tmp_path/'good',backend='lean',time_limit=300,keep_artifacts=True)
    assert good['status']=='ok',good
    p.write_text(source.replace('total += 1','total += 2'))
    bad=verify(p,tmp_path/'bad',backend='lean',time_limit=300,keep_artifacts=True)
    assert bad['status']=='failed',bad

@pytest.mark.parametrize("message", ['f"Bad {x:{widths[0]}}"', 'f"Bad {x!r}"'])
def test_exception_formatting_is_rejected(message):
    source = "#@ ensures True\ndef reject(x: int, widths: list[int]) -> None:\n    raise ValueError(" + message + ")\n"
    with pytest.raises(EncodeError):
        encode_imperative(source,parse_source(source),'formatting.py')

@pytest.mark.skipif(find_lean() is None,reason='Lean unavailable')
def test_scalar_whole_function_proof_checks_body(tmp_path):
    from veripy.api import verify
    source = "#@ requires x >= 0\n#@ ensures result == x * x\ndef square(x: int) -> int:\n    return x * x\n"
    p=tmp_path/'square.py';p.write_text(source)
    p.with_suffix('.proofs.lean').write_text('theorem square__proof (x : Int) (h : x ≥ 0) : x*x=x*x := by rfl\n')
    good=verify(p,tmp_path/'good',backend='lean',time_limit=120,keep_artifacts=True)
    assert good['status']=='ok',good
    p.write_text(source.replace('return x * x','return x * x + 1'))
    bad=verify(p,tmp_path/'bad',backend='lean',time_limit=120,keep_artifacts=True)
    assert bad['status']=='failed',bad
