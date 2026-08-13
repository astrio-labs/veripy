"""The agent interface: structured failures from `lemmapy verify --json`."""

import json
from pathlib import Path

import pytest

from lemmapy.agentio import verify_structured
from lemmapy.backends.dafny.driver import classify_obligation, find_dafny
from lemmapy.cli import main

BROKEN_CLAMP = (
    "#@ requires lo <= hi\n"
    "#@ ensures lo <= result <= hi\n"
    "def clamp(x: int, lo: int, hi: int) -> int:\n"
    "    return x\n"
)

GOOD = (
    "#@ ensures result == x + 1\n"
    "def bump(x: int) -> int:\n"
    "    return x + 1\n"
)


def test_classify_obligation_kinds():
    cases = {
        "a postcondition could not be proved on this return path": "postcondition",
        "this loop invariant could not be proved on entry": "invariant",
        "assertion might not hold": "assertion",
        "a precondition for this call could not be proved": "call-precondition",
        "cannot prove termination; try supplying a decreases clause": "termination",
        "verification timed out": "timeout",
        "something novel": "unknown",
    }
    for message, kind in cases.items():
        assert classify_obligation(message) == kind, message


def test_encode_error_is_a_structured_payload(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return len(set(xs))\n"
    )
    payload = verify_structured(src, tmp_path / "out")
    assert payload["status"] == "encode-error"
    failure = payload["failures"][0]
    assert failure["kind"] == "conformance" and failure["py_line"] == 3


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_failed_proof_yields_obligation_and_spans(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(BROKEN_CLAMP)
    payload = verify_structured(src, tmp_path / "out")
    assert payload["status"] == "failed"
    failure = payload["failures"][0]
    assert failure["kind"] == "postcondition"
    assert failure["function"] == "clamp"
    assert failure["py_line"] == 4  # the return path
    assert failure["dafny_line"] > 0
    assert payload["sidecar"]["exists"] is False


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_ok_payload_and_cli_exit_codes(tmp_path, capsys):
    good = tmp_path / "good.py"
    good.write_text(GOOD)
    out = tmp_path / "failures.json"
    status = main(["verify", str(good), "-o", str(tmp_path / "o"),
                   "--no-types", "--json", str(out)])
    assert status == 0
    payloads = json.loads(out.read_text())
    assert payloads[0]["status"] == "ok" and payloads[0]["failures"] == []

    bad = tmp_path / "bad.py"
    bad.write_text(BROKEN_CLAMP)
    status = main(["verify", str(bad), "-o", str(tmp_path / "o2"),
                   "--no-types", "--json", str(out)])
    assert status == 1
    payloads = json.loads(out.read_text())
    assert payloads[0]["status"] == "failed"


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_sidecar_state_travels_with_the_payload(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    (tmp_path / "m.proofs.dfy").write_text(
        "lemma Trivial(x: int)\n  ensures x == x\n{\n}\n"
    )
    payload = verify_structured(src, tmp_path / "out")
    assert payload["status"] == "ok"
    assert payload["sidecar"]["exists"] is True
    assert payload["sidecar"]["lemmas"] == ["Trivial"]
    assert "Trivial" in payload["sidecar"]["text"]
