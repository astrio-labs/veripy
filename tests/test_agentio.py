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


def test_payload_carries_toolchain_provenance(tmp_path):
    # A host embedding this backend must be able to tell whether two "ok"
    # verdicts meant the same thing — provenance rides the MACHINE payload,
    # not only the human report, and is present on every outcome.
    from lemmapy.backends.dafny.preamble import PREAMBLE_VERSION

    src = tmp_path / "m.py"
    src.write_text(GOOD)
    payload = verify_structured(src, tmp_path / "out")
    assert payload["toolchain"]["preamble_version"] == PREAMBLE_VERSION
    assert "dafny_version" in payload["toolchain"]

    # ...including on a non-ok outcome (unreadable source -> tool-error).
    missing = tmp_path / "nope.py"
    bad = verify_structured(missing, tmp_path / "out2")
    assert bad["status"] == "tool-error"
    assert bad["toolchain"]["preamble_version"] == PREAMBLE_VERSION


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


def test_malformed_source_is_a_structured_payload(tmp_path):
    src = tmp_path / "m.py"
    src.write_text("def broken(:\n")
    payload = verify_structured(src, tmp_path / "out")
    assert payload["status"] == "spec-error"
    assert payload["failures"][0]["kind"] == "syntax"


def test_gate_diagnostics_attributed_to_requested_relative_path(tmp_path, capsys, monkeypatch):
    from lemmapy.frontend.typegate import find_basedpyright

    if find_basedpyright() is None:
        pytest.skip("basedpyright not installed")
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode": "strict"}\n')
    (tmp_path / "m.py").write_text(
        "#@ ensures result >= 0 or result < 0\ndef f(x):\n    return x\n")
    monkeypatch.chdir(tmp_path)
    out = tmp_path / "failures.json"
    status = main(["verify", "m.py", "-o", str(tmp_path / "o"),
                   "--json", str(out)])
    assert status == 2
    payloads = json.loads(out.read_text())
    # One payload, keyed by the path the caller asked about, carrying the
    # diagnostics (not an empty entry plus a phantom absolute-path entry).
    assert len(payloads) == 1
    assert payloads[0]["file"] == "m.py"
    assert payloads[0]["failures"]


def test_undecodable_source_is_a_tool_error(tmp_path):
    src = tmp_path / "m.py"
    src.write_bytes(b"\xff\xfe broken")
    payload = verify_structured(src, tmp_path / "out")
    assert payload["status"] == "tool-error"
    assert "unreadable source" in payload["error"]


def test_path_aliases_both_carry_gate_diagnostics(tmp_path, monkeypatch):
    from lemmapy.frontend.typegate import find_basedpyright

    if find_basedpyright() is None:
        pytest.skip("basedpyright not installed")
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode": "strict"}\n')
    (tmp_path / "m.py").write_text(
        "#@ ensures result >= 0 or result < 0\ndef f(x):\n    return x\n")
    monkeypatch.chdir(tmp_path)
    out = tmp_path / "failures.json"
    # Two genuinely distinct spellings of one file (Path() normalizes
    # ./m.py to m.py, so use relative + absolute).
    absolute = str(tmp_path / "m.py")
    status = main(["verify", "m.py", absolute, "-o", str(tmp_path / "o"),
                   "--json", str(out)])
    assert status == 2
    payloads = json.loads(out.read_text())
    assert {p["file"] for p in payloads} == {"m.py", absolute}
    assert all(p["failures"] for p in payloads)


def test_tokenizer_valueerror_is_a_structured_payload(tmp_path):
    src = tmp_path / "m.py"
    src.write_bytes(b"def f():\x00\n    pass\n")
    payload = verify_structured(src, tmp_path / "out")
    assert payload["status"] == "spec-error"
    assert payload["failures"][0]["kind"] == "syntax"


def test_unwritable_json_destination_is_a_controlled_exit(tmp_path, capsys):
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    blocker = tmp_path / "blocked"
    blocker.write_text("")
    status = main(["verify", str(src), "-o", str(tmp_path / "o"),
                   "--no-types", "--json", str(blocker / "out.json")])
    assert status == 2
    assert "cannot write" in capsys.readouterr().err


def test_unwritable_outdir_is_a_tool_error(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    blocker = tmp_path / "blocked"
    blocker.write_text("")  # a file where the outdir must be a directory
    payload = verify_structured(src, blocker / "sub")
    assert payload["status"] == "tool-error"


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_same_stem_files_get_distinct_stubs(tmp_path):
    from lemmapy.agentio import verify_structured_many

    a_dir, b_dir = tmp_path / "a", tmp_path / "b"
    a_dir.mkdir(), b_dir.mkdir()
    (a_dir / "m.py").write_text(GOOD)
    (b_dir / "m.py").write_text(BROKEN_CLAMP)
    payloads = verify_structured_many(
        [a_dir / "m.py", b_dir / "m.py"], tmp_path / "out")
    assert payloads[0]["stub"] != payloads[1]["stub"]
    assert payloads[0]["status"] == "ok" and payloads[1]["status"] == "failed"


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_sidecar_region_failures_not_attributed_to_functions(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    (tmp_path / "m.proofs.dfy").write_text(
        "lemma Bogus(x: int)\n  ensures x > 0\n{\n}\n")
    payload = verify_structured(src, tmp_path / "out")
    assert payload["status"] == "failed"
    assert all(f["region"] == "sidecar" and f["function"] is None
               for f in payload["failures"])


def test_gate_failure_still_writes_json(tmp_path, capsys):
    from lemmapy.frontend.typegate import find_basedpyright

    if find_basedpyright() is None:
        pytest.skip("basedpyright not installed")
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode": "strict"}\n')
    src = tmp_path / "m.py"
    src.write_text("#@ ensures result >= 0 or result < 0\ndef f(x):\n    return x\n")
    out = tmp_path / "failures.json"
    status = main(["verify", str(src), "-o", str(tmp_path / "o"),
                   "--json", str(out)])
    assert status == 2
    payloads = json.loads(out.read_text())
    assert payloads and payloads[0]["status"] == "gate-error"


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
