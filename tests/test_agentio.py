"""The agent interface: structured failures from `veripy verify --json`."""

import json
from pathlib import Path

import pytest

from veripy.agentio import verify_structured
from veripy.backends.dafny.driver import classify_obligation, find_dafny
from veripy.cli import main

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
        # Dafny does not repeat "loop invariant" for the maintenance case,
        # so a needle of "loop invariant" let the MORE COMMON of the two
        # fall through to `unknown` -- which is outside PROVER_KINDS, so a
        # pack whose whole job is maintaining an invariant read as no
        # evidence of a proof at all.
        "this invariant could not be proved to be maintained by the loop":
            "invariant",
        "assertion might not hold": "assertion",
        "a precondition for this call could not be proved": "call-precondition",
        # The FUNCTION variant is phrased without "call"; it fell through
        # to `unknown` until the dual-adjudication reclassification
        # surfaced it on live prover output.
        "function precondition could not be proved": "call-precondition",
        "cannot prove termination; try supplying a decreases clause": "termination",
        "verification timed out": "timeout",
        "something novel": "unknown",
        # A resolution error whose text happens to name an obligation is
        # still a resolution error: the proof was never attempted. These
        # are matched first, which is what the table's comment always
        # claimed while the entries sat below the obligation patterns.
        "unresolved identifier: InvariantHelper": "resolution",
        "wrong number of arguments (postcondition helper)": "resolution",
    }
    for message, kind in cases.items():
        assert classify_obligation(message) == kind, message


def test_payload_carries_toolchain_provenance(tmp_path):
    # A host embedding this backend must be able to tell whether two "ok"
    # verdicts meant the same thing — provenance rides the MACHINE payload,
    # not only the human report, and is present on every outcome.
    from veripy.backends.dafny.preamble import PREAMBLE_VERSION

    src = tmp_path / "m.py"
    src.write_text(GOOD)
    payload = verify_structured(src, tmp_path / "out")
    assert payload["toolchain"]["preamble_version"] == PREAMBLE_VERSION
    assert "dafny_version" in payload["toolchain"]

    # ...including on a non-ok outcome (unreadable source -> tool-error).
    # The prover never ran there, so its version is None and — importantly —
    # is never queried: an immediate error must not wait on a subprocess.
    missing = tmp_path / "nope.py"
    from veripy.backends.base import get_backend

    # Count calls at the backend seam (what the pipeline actually calls);
    # the module-level `dafny_version` import is transitional and inert.
    be = get_backend("dafny")
    called = {"n": 0}
    real = be.prover_version
    be.prover_version = lambda: (called.__setitem__("n", called["n"] + 1)
                                 or "never")
    try:
        bad = verify_structured(missing, tmp_path / "out2")
    finally:
        be.prover_version = real
    assert bad["status"] == "tool-error"
    assert bad["toolchain"]["preamble_version"] == PREAMBLE_VERSION
    assert bad["toolchain"]["dafny_version"] is None
    assert called["n"] == 0


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
    from veripy.frontend.typegate import find_basedpyright

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
    from veripy.frontend.typegate import find_basedpyright

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
    from veripy.agentio import verify_structured_many

    a_dir, b_dir = tmp_path / "a", tmp_path / "b"
    a_dir.mkdir(), b_dir.mkdir()
    (a_dir / "m.py").write_text(GOOD)
    (b_dir / "m.py").write_text(BROKEN_CLAMP)
    payloads = verify_structured_many(
        [a_dir / "m.py", b_dir / "m.py"], tmp_path / "out",
        keep_artifacts=True)
    assert payloads[0]["stub"] != payloads[1]["stub"]
    assert payloads[0]["status"] == "ok" and payloads[1]["status"] == "failed"


def test_artifacts_are_cleaned_unless_requested(tmp_path):
    """Private staging must not grow `outdir` without bound.

    Per-invocation directories fixed a soundness race, but a backend
    verifying continuously would accumulate one directory per call — where
    the old shared path was at least capped by the number of distinct
    stems. Artifacts are diagnostic only, so they are cleaned by default.
    """
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    out = tmp_path / "out"

    for _ in range(3):
        payload = verify_structured(src, out)
        assert payload["artifacts_kept"] is False
        # No dangling path is advertised when the directory is gone.
        assert payload["stub"] is None
    assert list(out.iterdir()) == [], "scratch directories accumulated"

    kept = verify_structured(src, out, keep_artifacts=True)
    assert kept["artifacts_kept"] is True
    assert kept["stub"] is not None and Path(kept["stub"]).exists()
    assert len(list(out.iterdir())) == 1


def test_kept_artifacts_are_content_addressed_not_per_run(tmp_path):
    """Retention must not mean accumulation.

    The CLI keeps artifacts so a human can open the printed stub path, but
    a per-run directory name would leave one behind every invocation. The
    name is derived from the stub's content instead: re-running an
    unchanged file overwrites its own directory, while a different file
    (including a same-stemmed one from elsewhere) still gets its own — the
    collision that let one verification certify another's code.
    """
    a_dir, b_dir = tmp_path / "a", tmp_path / "b"
    a_dir.mkdir(), b_dir.mkdir()
    (a_dir / "m.py").write_text(GOOD)
    (b_dir / "m.py").write_text(BROKEN_CLAMP)
    out = tmp_path / "out"

    first = verify_structured(a_dir / "m.py", out, keep_artifacts=True)
    for _ in range(4):
        again = verify_structured(a_dir / "m.py", out, keep_artifacts=True)
        assert again["stub"] == first["stub"], "re-run moved to a new directory"
    assert len(list(out.iterdir())) == 1, "re-runs accumulated directories"

    other = verify_structured(b_dir / "m.py", out, keep_artifacts=True)
    assert other["stub"] != first["stub"]
    assert len(list(out.iterdir())) == 2

    # Editing the file re-addresses it, so a stale stub is never reused.
    (a_dir / "m.py").write_text(GOOD.replace("x + 1", "x + 2"))
    edited = verify_structured(a_dir / "m.py", out, keep_artifacts=True)
    assert edited["stub"] != first["stub"]


def test_plain_write_text_has_an_observable_truncation_window(tmp_path):
    """Why the stub is written atomically, demonstrated rather than asserted.

    Opening for write truncates IMMEDIATELY, before any content is
    produced. A concurrent reader — the Dafny process we launch on the
    stub — can therefore observe an empty file. Content-addressing makes
    two writers agree on the final bytes, but says nothing about what a
    reader sees in between.
    """
    target = tmp_path / "stub.dfy"
    target.write_text("method Complete() { }\n")
    handle = open(target, "w")          # what write_text does first
    try:
        assert target.read_text() == "", (
            "expected an observable truncation window; if this ever fails, "
            "the atomicity argument for atomic_write_text needs revisiting")
    finally:
        handle.close()


def test_atomic_write_never_leaves_a_partial_target(tmp_path, monkeypatch):
    """The property the fix actually provides.

    A concurrency test cannot reliably schedule itself into a
    sub-millisecond window, so the guarantee is pinned directly: a write
    that dies partway must leave the target untouched and no debris
    behind — never a truncated stub for Dafny to read.
    """
    import veripy.agentio as mod
    from veripy.agentio import atomic_write_text

    target = tmp_path / "stub.dfy"
    target.write_text("method Complete() { }\n")

    class Boom(Exception):
        pass

    real_named_temp = mod.tempfile.NamedTemporaryFile

    def exploding(*args, **kwargs):
        handle = real_named_temp(*args, **kwargs)
        original_write = handle.write

        def half_then_fail(text):
            original_write(text[: len(text) // 2])
            raise Boom("disk full mid-write")

        handle.write = half_then_fail
        return handle

    monkeypatch.setattr(mod.tempfile, "NamedTemporaryFile", exploding)
    with pytest.raises(Boom):
        atomic_write_text(target, "method Replacement() { }\n" * 50)

    assert target.read_text() == "method Complete() { }\n", (
        "a failed write corrupted the target")
    assert not [f for f in tmp_path.iterdir() if f.name.endswith(".tmp")], (
        "a failed write left a temp file behind")


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_concurrent_retained_verifications_share_one_directory(tmp_path):
    # A smoke test, not a race reproduction: four retained verifications of
    # one module must all succeed, address the same content-addressed
    # directory, and leave no temp debris.
    import concurrent.futures

    src = tmp_path / "m.py"
    src.write_text(GOOD)
    out = tmp_path / "out"

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        payloads = list(pool.map(
            lambda _i: verify_structured(src, out, time_limit=60,
                                         keep_artifacts=True),
            range(4)))
    for p in payloads:
        assert p["status"] == "ok", (
            f"a verifying module reported {p['status']} "
            f"({p.get('error') or p['failures']})")
    assert len({p["stub"] for p in payloads}) == 1
    assert len(list(out.iterdir())) == 1
    stub_dir = Path(payloads[0]["stub"]).parent
    assert not [f for f in stub_dir.iterdir() if f.name.endswith(".tmp")]


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_concurrent_same_stem_verifications_do_not_swap_verdicts(tmp_path):
    """The soundness case: a shared outdir must not let one verification
    certify another's code.

    The stub used to be written to `outdir/<stem>.dfy`, so two concurrent
    verifications of same-stemmed modules raced on one file and Dafny read
    whichever was written last. Both directions were silent and produced
    well-formed payloads: the BROKEN module came back `ok`, and the correct
    module came back `failed` carrying the other file's failures. An
    embedding host shares one scratch directory across callers by nature,
    so this is a soundness break rather than untidiness.
    """
    import concurrent.futures

    a_dir, b_dir = tmp_path / "a", tmp_path / "b"
    a_dir.mkdir(), b_dir.mkdir()
    (a_dir / "m.py").write_text(GOOD)          # verifies
    (b_dir / "m.py").write_text(BROKEN_CLAMP)  # violates its ensures
    shared = tmp_path / "shared-out"

    # Repeat: the race is timing-dependent and one pass can pass by luck.
    for _ in range(4):
        # keep_artifacts so the stub paths survive to be compared — that
        # uniqueness is what the race violated.
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            futures = [pool.submit(verify_structured, d / "m.py", shared,
                                   time_limit=60, keep_artifacts=True)
                       for d in (a_dir, b_dir)]
            good, broken = (f.result() for f in futures)
        assert good["status"] == "ok", (
            f"correct module reported {good['status']} with failures "
            f"{good['failures']} — verdict came from the other file's stub")
        assert broken["status"] == "failed", (
            "a module that violates its postcondition was reported "
            f"{broken['status']} — unverified code certified")
        # Stub paths must be unique, or the payload's own reference is stale.
        assert good["stub"] != broken["stub"]
        assert all(f["function"] == "clamp" for f in broken["failures"])


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
    from veripy.frontend.typegate import find_basedpyright

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


RECORD_KEYS = {"kind", "rule", "function", "region", "py_line", "dafny_line",
               "message"}


def _statuses_with_records(tmp_path):
    """One payload per status that produces failure records."""
    out = tmp_path / "out"
    cases = {}

    syntax = tmp_path / "syn.py"
    syntax.write_text("def f(:\n")
    cases["spec-error/syntax"] = verify_structured(syntax, out)

    bad_clause = tmp_path / "cl.py"
    bad_clause.write_text("#@ ensures ???\ndef f() -> int:\n    return 0\n")
    cases["spec-error/spec"] = verify_structured(bad_clause, out)

    outside = tmp_path / "frag.py"
    outside.write_text(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    xs[0] = 1\n"
        "    return xs[0]\n")
    cases["encode-error"] = verify_structured(outside, out)
    return cases


def test_every_failure_record_has_the_same_shape(tmp_path):
    """A consumer written against one status must not break on another.

    `encode-error` and `spec-error` records used to omit the
    `function`/`region`/`dafny_line` keys that `failed` records carry, so a
    client reading `record["function"]` raised KeyError depending on which
    way verification went.
    """
    for label, payload in _statuses_with_records(tmp_path).items():
        assert payload["failures"], f"{label} produced no actionable record"
        for record in payload["failures"]:
            assert set(record) == RECORD_KEYS, f"{label} record shape differs"


def test_fragment_rejections_carry_a_machine_readable_rule(tmp_path):
    """Routing must not require regexing English.

    Rejection messages are prose and may be reworded; `rule` is the stable
    id an embedding host keys on.
    """
    out = tmp_path / "out"
    src = tmp_path / "m.py"
    src.write_text(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    xs[0] = 1\n"
        "    return xs[0]\n")
    payload = verify_structured(src, out)
    assert payload["status"] == "encode-error"
    (record,) = payload["failures"]
    assert record["rule"] == "indexed-assignment"
    # The message must not contradict itself by listing the construct it
    # has just rejected as admitted.
    assert "indexed assignment" in record["message"]
    assert "-- admitted: assignment" not in record["message"]


def test_unsupported_type_and_call_get_distinct_rules(tmp_path):
    out = tmp_path / "out"
    dict_src = tmp_path / "d.py"
    dict_src.write_text(
        "#@ ensures result >= 0\n"
        "def f(d: dict[str, int]) -> int:\n"
        "    return 0\n")
    dict_payload = verify_structured(dict_src, out)
    assert dict_payload["status"] == "encode-error"
    assert dict_payload["failures"][0]["rule"] is not None

    call_src = tmp_path / "c.py"
    call_src.write_text(
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return len(reversed(xs))\n")
    call_payload = verify_structured(call_src, out)
    assert call_payload["status"] == "encode-error"
    assert call_payload["failures"][0]["rule"] is not None
