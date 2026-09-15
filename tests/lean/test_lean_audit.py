"""Adversarial driver checks: a hung/lying prover must not produce an audited proof."""
import json
import subprocess
import sys
import time
from pathlib import Path
from types import SimpleNamespace

from veripy.backends.lean import driver
from veripy.backends.lean.backend import LeanBackend


def test_wall_limit_kills_prover_and_preserves_partial_output(tmp_path, monkeypatch):
    fake = tmp_path / 'slow-lean'
    fake.write_text(f'#!{sys.executable}\nimport time\nprint("partial diagnostic",flush=True)\ntime.sleep(20)\n')
    fake.chmod(0o755)
    monkeypatch.setattr(driver, 'find_lean', lambda: str(fake))
    start = time.monotonic()
    result = driver.verify_lean_file(tmp_path / 'input.lean', {}, time_limit=1)
    assert time.monotonic() - start < 5
    assert not result.ok and result.error is None
    assert result.diagnostics[0].obligation == 'timeout'
    assert 'partial diagnostic' in result.raw


def test_success_without_requested_axiom_audit_is_rejected(tmp_path, monkeypatch):
    artifact = tmp_path / 'input.lean'
    artifact.write_text('theorem proof : True := by trivial\n#print axioms proof\n')
    monkeypatch.setattr(driver, 'find_lean', lambda: 'lean')
    monkeypatch.setattr(driver.subprocess, 'run', lambda *a, **kw:
                        SimpleNamespace(returncode=0, stdout='', stderr=''))
    result = driver.verify_lean_file(artifact, {})
    assert not result.ok
    assert 'missing axiom audit' in result.diagnostics[-1].message


def test_successful_check_retains_raw_log_and_axioms(tmp_path, monkeypatch):
    artifact = tmp_path / 'input.lean'
    artifact.write_text('theorem proof : True := by trivial\n#print axioms proof\n')
    diagnostic = {'severity':'information','pos':{'line':2},
                  'data':"'proof' does not depend on any axioms"}
    output = json.dumps(diagnostic) + '\n'
    monkeypatch.setattr(driver, 'find_lean', lambda: 'lean')
    monkeypatch.setattr(driver.subprocess, 'run', lambda *a, **kw:
                        SimpleNamespace(returncode=0, stdout=output, stderr=''))
    result = LeanBackend().verify_artifact(artifact, {}, time_limit=3, extent=2)
    assert result.ok
    assert Path(result.log_path).read_text() == output
    audit = json.loads(Path(result.audit_path).read_text())
    assert audit['ok'] and audit['axiom_messages'] == [diagnostic['data']]
    assert audit['wall_limit_seconds'] == 3
    other = LeanBackend().verify_artifact(artifact, {}, time_limit=4, extent=2)
    assert other.log_path != result.log_path and Path(result.audit_path).exists()


def test_comment_delimiters_in_strings_do_not_hide_commands():
    import pytest
    from veripy.backends.lean.sidecar import validate_sidecar_text
    from veripy.backends.dafny.encoder import EncodeError
    text = 'def a : String := "/-"\naxiom falsehood : False\ndef b : String := "-/"\n'
    with pytest.raises(EncodeError, match='not allowed'):
        validate_sidecar_text(text, 'attack.lean')


def test_nested_comments_and_meta_execution():
    import pytest
    from veripy.backends.lean.sidecar import validate_sidecar_text
    from veripy.backends.dafny.encoder import EncodeError
    assert 'safe' in validate_sidecar_text('/- outer /- inner -/ axiom ignored -/\ntheorem safe : True := by trivial', 'safe.lean')
    for command in ['run_tac', 'run_elab', 'initialize', 'builtin_initialize']:
        with pytest.raises(EncodeError, match='not allowed'):
            validate_sidecar_text(f'theorem safe : True := by trivial\n{command} pure ()', 'attack.lean')


def test_packaged_libraries_are_closed_and_self_contained(tmp_path):
    import pytest
    from veripy.backends.lean.sidecar import load_lean_sidecar
    from veripy.backends.dafny.encoder import EncodeError
    p = tmp_path / 'case.py'
    p.with_suffix('.proofs.lean').write_text('-- VERIPY LIBRARY arithmetic\ntheorem example : True := by trivial\n')
    pack = load_lean_sidecar(p)
    assert 'FloorDivFacts' in pack.lemmas
    assert 'Int.fdiv_mul_add_fmod' in pack.text
    p.with_suffix('.proofs.lean').write_text('-- VERIPY LIBRARY ../../outside\ntheorem example : True := by trivial\n')
    with pytest.raises(EncodeError, match='unknown Lean proof library'):
        load_lean_sidecar(p)


def test_ci_wall_stops_the_prover_process_group(tmp_path):
    import importlib.util
    path = Path(__file__).resolve().parents[2] / 'case_studies/tools/run_matrix.py'
    spec = importlib.util.spec_from_file_location('parity_runner', path)
    module = importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    marker = tmp_path / 'child-survived'
    child = f'import time;from pathlib import Path;time.sleep(1);Path({str(marker)!r}).write_text("alive")'
    parent = 'import subprocess,sys,time;subprocess.Popen([sys.executable,"-c",'+repr(child)+']);time.sleep(20)'
    status, output, elapsed, timed_out = module.run_bounded([sys.executable,'-c',parent],0.2,tmp_path)
    assert timed_out and status != 0 and elapsed < 5
    time.sleep(1.2)
    assert not marker.exists()


def test_hidden_hypothesis_injection_is_rejected_before_proving(tmp_path):
    from veripy.api import verify
    path = tmp_path / 'case.py'
    path.write_text('#@ ensures result == x + 2\ndef bump(x: int) -> int:\n    return x + 1\n')
    path.with_suffix('.proofs.lean').write_text('section\nvariable (hidden : False)\ninclude hidden\ntheorem innocent : True := by trivial\n')
    result = verify(path,tmp_path/'proof',backend='lean',keep_artifacts=True)
    assert result['status'] == 'encode-error'
    assert any(f['rule']=='lean-sidecar' for f in result['failures'])


def test_ambient_context_commands_are_not_proof_declarations():
    import pytest
    from veripy.backends.lean.sidecar import validate_sidecar_text
    from veripy.backends.dafny.encoder import EncodeError
    for command in ['namespace Trap','section','variable (h : False)','include h','open Trap','attribute [simp] evil','export Trap (evil)']:
        with pytest.raises(EncodeError,match='ambient command'):
            validate_sidecar_text(command+'\ntheorem innocent : True := by trivial','attack.lean')


def test_quoted_identifiers_cannot_hide_commands():
    import pytest
    from veripy.backends.lean.sidecar import validate_sidecar_text
    from veripy.backends.dafny.encoder import EncodeError
    text = 'def «/-» : Nat := 0\naxiom falsehood : False\ndef «-/» : Nat := 0\n'
    with pytest.raises(EncodeError,match='not allowed'):
        validate_sidecar_text(text,'attack.lean')


def test_character_quote_does_not_change_comment_state():
    from veripy.backends.lean.sidecar import _strip_comments
    text = "def quote : Char := '\"'\n/- axiom inside comment -/\ntheorem safe : True := by trivial\n"
    stripped = _strip_comments(text)
    assert 'axiom' not in stripped and 'theorem safe' in stripped


def test_sidecar_cannot_stop_or_suppress_generated_checks():
    import pytest
    from veripy.backends.lean.sidecar import validate_sidecar_text
    from veripy.backends.dafny.encoder import EncodeError
    for command in ['#exit','#guard_msgs in','#print innocent']:
        with pytest.raises(EncodeError,match='only #print axioms'):
            validate_sidecar_text('theorem innocent : True := by trivial\n'+command,'attack.lean')


def test_axiom_audit_handles_primed_theorem_names():
    assert driver.axiom_violations(["'proof'' depends on axioms: [sorryAx]"]) == [("proof'",['sorryAx'])]


def test_elaborator_and_initializer_attributes_are_rejected():
    import pytest
    from veripy.backends.lean.sidecar import validate_sidecar_text
    from veripy.backends.dafny.encoder import EncodeError
    for attribute in ['command_elab Foo','simp_proc Foo','init']:
        with pytest.raises(EncodeError,match='only spec/simp/grind attributes'):
            validate_sidecar_text('@['+attribute+']\ntheorem innocent : True := by trivial','attack.lean')
    assert 'safe' in validate_sidecar_text('@[simp]\ntheorem safe : True := by trivial','safe.lean')
