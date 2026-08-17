"""The Lean backend, slice 1: loop-free integer functions behind the
`ProofBackend` seam.

Split by dependency: encoder and classifier tests are pure Python (they
run everywhere, CI included); end-to-end tests need `lean` on PATH and
carry the house skipif. Every live assertion here was first pinned
against a real Lean 4.33 run.
"""

from pathlib import Path

import pytest

from lemmapy.backends.base import available_backends, get_backend
from lemmapy.backends.dafny.encoder import EncodeError
from lemmapy.backends.lean.backend import LeanBackend
from lemmapy.backends.lean.driver import classify_lean_message, find_lean
from lemmapy.backends.lean.encoder import encode_module_lean
from lemmapy.frontend.extract import parse_source

BUMP = ("#@ ensures result == x + 1\n"
        "def bump(x: int) -> int:\n"
        "    return x + 1\n")

CLAMP = ("#@ requires lo <= hi\n"
         "#@ ensures lo <= result <= hi\n"
         "def clamp(x: int, lo: int, hi: int) -> int:\n"
         "    if x < lo:\n"
         "        return lo\n"
         "    if x > hi:\n"
         "        return hi\n"
         "    return x\n")


def _encode(source: str):
    return encode_module_lean(source, parse_source(source),
                              module_name="m.py")


def test_registry_serves_lean():
    assert "lean" in available_backends()
    be = get_backend("lean")
    assert isinstance(be, LeanBackend)
    assert be is get_backend("lean")
    assert be.artifact_name("task") == "task.lean"
    assert be.sidecar_path(Path("/x/t.py")) == Path("/x/t.proofs.lean")


def test_encoder_emits_def_and_spec_theorem():
    enc = _encode(BUMP)
    assert "def bump (x : Int) : Int :=" in enc.lean_source
    assert "theorem bump_spec (x : Int) :" in enc.lean_source
    assert "(bump x) = (x + 1)" in enc.lean_source
    assert enc.theorems == ["bump_spec"]
    # The tactic lines map to the ensures clause, so a failing proof
    # points at the contract, not at Lean plumbing.
    tactic_line = next(i for i, text in
                       enumerate(enc.lean_source.split("\n"), start=1)
                       if "all_goals omega" in text)
    assert enc.line_map[tactic_line] == 1  # ensures is source line 1


def test_encoder_compiles_if_chains_and_requires():
    enc = _encode(CLAMP)
    assert "if (x < lo) then lo else" in enc.lean_source
    assert "(h0 : (lo ≤ hi))" in enc.lean_source
    # The chained comparison becomes a conjunction over the application.
    assert "(clamp x lo hi)" in enc.lean_source
    assert "∧" in enc.lean_source


def test_encoder_rejects_out_of_slice_loudly():
    loops = ("#@ ensures result >= 0\n"
             "def f(n: int) -> int:\n"
             "    s = 0\n"
             "    for i in range(n):\n"
             "        s = s + i\n"
             "    return s\n")
    with pytest.raises(EncodeError) as exc:
        _encode(loops)
    assert exc.value.rule == "lean-slice-1"
    assert "loop" in exc.value.message.lower()

    reassign = ("#@ ensures result == x\n"
                "def f(x: int) -> int:\n"
                "    x = x + 1\n"
                "    return x - 1\n")
    with pytest.raises(EncodeError, match="immutable"):
        _encode(reassign)


def test_classifier_maps_live_lean_messages():
    # Pinned from live Lean 4.33 output: omega's failure text, which is
    # NOT "unsolved goals" (the first classifier draft missed it and a
    # false spec came back kind=unknown).
    assert classify_lean_message(
        "omega could not prove the goal:\nNo usable constraints found."
    ) == "postcondition"
    assert classify_lean_message("unsolved goals\n⊢ False") == "postcondition"
    assert classify_lean_message("unknown identifier 'PyFoo'") == "resolution"
    assert classify_lean_message(
        "(deterministic) timeout at `whnf`, maxHeartbeats") == "timeout"
    assert classify_lean_message("something novel") == "unknown"


def test_lean_sidecars_are_refused_not_ignored(tmp_path):
    # A user who wrote lemmas must never believe they were used.
    src = tmp_path / "t.py"
    src.write_text(BUMP)
    (tmp_path / "t.proofs.lean").write_text("theorem helper : True := trivial\n")
    be = get_backend("lean")
    with pytest.raises(EncodeError, match="P3"):
        be.load_sidecar(src)
    with pytest.raises(EncodeError, match="P3"):
        be.validate_sidecar("lemma L : True := trivial")
    be.validate_sidecar("")  # the empty sidecar every slice-1 run stages


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_true_spec_verifies(tmp_path):
    from lemmapy.agentio import verify_structured

    src = tmp_path / "m.py"
    src.write_text(CLAMP)
    payload = verify_structured(src, tmp_path / "out", backend="lean")
    assert payload["status"] == "ok"
    assert payload["toolchain"]["dafny_version"]  # lean's version string


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_false_spec_fails_as_postcondition(tmp_path):
    from lemmapy.agentio import verify_structured

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == x + 2\n"
                   "def bump(x: int) -> int:\n"
                   "    return x + 1\n")
    payload = verify_structured(src, tmp_path / "out", backend="lean")
    assert payload["status"] == "failed"
    failure = payload["failures"][0]
    assert failure["kind"] == "postcondition"
    assert failure["py_line"] == 1  # the ensures clause, not Lean plumbing
