"""The proof-backend seam: one object per prover, selected by name.

P0 of the Lean track (ROADMAP): the protocol exists, Dafny sits behind
it, and NOTHING observable moves — the payloads a backend-threaded call
produces are identical to the pre-seam ones.
"""

from pathlib import Path

import pytest

from veripy.backends.base import (
    ProofBackend,
    available_backends,
    get_backend,
)
from veripy.backends.dafny.backend import DafnyBackend
from veripy.backends.dafny.driver import find_dafny
from veripy.backends.dafny.preamble import PREAMBLE_VERSION

GOOD = (
    "#@ ensures result == x + 1\n"
    "def bump(x: int) -> int:\n"
    "    return x + 1\n"
)


def test_get_backend_returns_cached_dafny_singleton():
    be = get_backend()
    assert isinstance(be, DafnyBackend)
    assert be is get_backend("dafny")  # cached, not re-built
    assert be.name == "dafny"
    assert be.preamble_version == PREAMBLE_VERSION


def test_unknown_backend_is_refused_with_the_known_set():
    # A typo must never silently fall back to another prover: the backend
    # name is provenance, and every payload built under it is labelled by
    # it (same principle as the engine layer's substitution guard).
    # ('coq' rather than 'lean': the Lean track's P1 registers lean, and
    # this test must keep refusing something.)
    with pytest.raises(ValueError, match="unknown backend 'coq'.*dafny"):
        get_backend("coq")


def test_dafny_backend_satisfies_the_protocol():
    be = get_backend()
    assert isinstance(be, ProofBackend)  # runtime_checkable structural check
    # The members the verify pipeline actually calls, spot-checked with
    # real semantics rather than presence alone.
    assert be.sidecar_path(Path("/x/task.py")) == Path("/x/task.proofs.dfy")
    assert be.artifact_name("task") == "task.dfy"
    with pytest.raises(Exception):  # bodiless lemma = axiom, whitelisted out
        be.validate_sidecar("lemma L(x: int)\n  ensures x == x\n")


def test_available_backends_lists_dafny():
    assert "dafny" in available_backends()


def test_backend_threaded_verify_is_byte_identical_to_default(tmp_path):
    # The P0 gate: threading the seam changes nothing observable. Same
    # module, default call vs explicit backend="dafny" — identical
    # payloads (the paths inside differ only via tmp staging, which the
    # payload does not expose when artifacts are not kept).
    from veripy.agentio import verify_structured

    src = tmp_path / "m.py"
    src.write_text(GOOD)
    a = verify_structured(src, tmp_path / "out-a")
    b = verify_structured(src, tmp_path / "out-b", backend="dafny")
    assert a == b
    assert a["toolchain"]["preamble_version"] == PREAMBLE_VERSION
    assert "dafny_version" in a["toolchain"]


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_cli_verify_accepts_backend_dafny(tmp_path):
    from veripy.cli import main

    src = tmp_path / "m.py"
    src.write_text(GOOD)
    out = tmp_path / "failures.json"
    status = main(["verify", str(src), "-o", str(tmp_path / "o"),
                   "--no-types", "--backend", "dafny", "--json", str(out)])
    assert status == 0


def test_cli_verify_refuses_unregistered_backend(tmp_path):
    # An unregistered backend is an argparse-level refusal (exit 2), so a
    # typo can never run under a silently-substituted prover. Needs no
    # prover installed: the refusal happens before any verification.
    from veripy.cli import main

    src = tmp_path / "m.py"
    src.write_text(GOOD)
    with pytest.raises(SystemExit) as exc:
        main(["verify", str(src), "-o", str(tmp_path / "o"),
              "--no-types", "--backend", "coq",
              "--json", str(tmp_path / "f.json")])
    assert exc.value.code == 2
