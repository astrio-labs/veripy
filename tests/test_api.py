"""The embedding surface: what a host program calls.

These tests pin the three properties that make the package usable inside
someone else's process — no printing, no exiting, expected failures as
values — because each is easy to break with an otherwise-reasonable edit.
"""

import io
import os
import sys
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

import pytest

import veripy
from veripy import api
from veripy.backends.dafny.driver import find_dafny
from veripy.failures import is_known

GOOD = "#@ ensures result == x + 1\ndef bump(x: int) -> int:\n    return x + 1\n"
OUTSIDE = ("#@ ensures result >= 0\n"
           "def f(xs: list[int]) -> int:\n"
           "    return len(set(xs))\n")


def _silently(fn, *args, **kwargs):
    """Run fn, returning (result, printed_text). A library that writes to
    stdout corrupts its host's output; one that writes to stderr pollutes
    its logs."""
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        result = fn(*args, **kwargs)
    return result, out.getvalue() + err.getvalue()


def test_root_does_not_shadow_submodules_with_api_names():
    # `veripy.repair` is a SUBMODULE. Re-exporting an api function of the
    # same name at the root makes `veripy.repair` a function or a module
    # depending on import order — this test pins the hazard so nobody
    # re-adds the convenience export.
    import veripy.repair as repair_module

    assert getattr(veripy, "repair") is repair_module
    assert not hasattr(veripy, "__all__"), (
        "the root must not advertise an api surface it cannot keep stable; "
        "the surface is veripy.api")
    for name in api.__all__:
        assert callable(getattr(api, name)), name


def test_api_never_prints(tmp_path):
    # Every operation, on both a good and a rejected input.
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    bad = tmp_path / "bad.py"
    bad.write_text(OUTSIDE)

    for path in (src, bad):
        for call in (lambda p: api.conformance(p),
                     lambda p: api.guard(p),
                     lambda p: api.verify(p, tmp_path / "w")):
            if call is not None and find_dafny() is None and "verify" in repr(call):
                continue
            _, printed = _silently(call, path)
            assert printed == "", f"{path.name}: wrote {printed!r}"
    _, printed = _silently(api.toolchain_info)
    assert printed == ""


def test_api_never_exits(tmp_path):
    # A SystemExit inside a host process is fatal to the host, so the
    # failure paths must return rather than exit.
    missing = tmp_path / "nope.py"
    for call in (lambda: api.conformance(missing),
                 lambda: api.guard(missing),
                 lambda: api.repair(missing, tmp_path / "w",
                                    engine="file:/nonexistent")):
        try:
            call()
        except SystemExit:  # pragma: no cover - the failure we are pinning
            pytest.fail("api raised SystemExit")


def test_expected_failures_are_values_with_published_kinds(tmp_path):
    outside = tmp_path / "bad.py"
    outside.write_text(OUTSIDE)
    result = api.conformance(outside)
    assert result["conformant"] is False
    assert result["functions"] == ["f"]
    assert all(is_known(f["kind"]) for f in result["failures"])
    assert result["failures"][0]["kind"] == "conformance"

    missing = api.conformance(tmp_path / "nope.py")
    assert missing["conformant"] is False
    assert all(is_known(f["kind"]) for f in missing["failures"])

    broken = tmp_path / "broken.py"
    broken.write_text("def f(:\n")
    assert api.conformance(broken)["failures"][0]["kind"] == "syntax"


def test_guard_reports_an_unparseable_module_as_a_value(tmp_path):
    # guard() used to call parse_source unguarded, so a malformed file threw
    # SyntaxError (or ValueError/TokenError) straight into the host — the one
    # thing property 3 says cannot happen. conformance() has always caught
    # these; guard() must too, or a host sweeping a directory dies on the
    # first unparseable file in it.
    broken = tmp_path / "broken.py"
    broken.write_text("def f(:\n")
    result = api.guard(broken)
    assert result == {"ok": False, "source": None,
                      "reason": "syntax error on line 1: invalid syntax"}

    nul = tmp_path / "nul.py"
    nul.write_bytes(b"def f():\n    return 0\n\x00\n")
    nul_result = api.guard(nul)
    assert nul_result["ok"] is False and nul_result["source"] is None
    # No lineno on this one; the reason must not say "line None".
    assert "None" not in nul_result["reason"], nul_result["reason"]


def test_repair_reports_a_filesystem_failure_as_a_value(tmp_path):
    # repair_file touches disk the host owns: the workdir, the sidecar beside
    # the source, and (apply=True) the source's directory. An OSError from any
    # of those used to escape repair() into the host.
    src = tmp_path / "m.py"
    src.write_text(GOOD)

    # A workdir that is a regular file: repair_file's mkdir raises before any
    # prover runs, so this pins the boundary without needing dafny.
    not_a_dir = tmp_path / "wfile"
    not_a_dir.write_text("x")
    result = api.repair(src, not_a_dir, engine="file:/nonexistent")
    assert result["verified"] is False and result["sidecar_text"] is None
    assert "filesystem error" in result["reason"]

    # An unreadable sidecar beside the source, read before the first verify.
    sidecar = tmp_path / "m.proofs.dfy"
    sidecar.write_text("lemma L() {}\n")
    sidecar.chmod(0o000)
    try:
        if os.access(sidecar, os.R_OK):  # pragma: no cover - root/odd fs
            pytest.skip("cannot make a file unreadable here")
        unreadable = api.repair(src, tmp_path / "w", engine="file:/nonexistent")
    finally:
        sidecar.chmod(0o644)
    assert unreadable["verified"] is False
    assert "filesystem error" in unreadable["reason"]


def test_conformance_accepts_a_module_in_the_fragment(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    assert api.conformance(src) == {"conformant": True, "functions": ["bump"],
                                    "failures": []}


def test_toolchain_info_is_comparable_across_runs():
    info = api.toolchain_info()
    assert set(info) == {"preamble_version", "dafny_version",
                         "taxonomy_version", "failure_kinds"}
    assert info["failure_kinds"] == sorted(info["failure_kinds"])
    assert "resolution" in info["failure_kinds"]


def test_guard_returns_source_rather_than_writing_it(tmp_path):
    # Where generated code lands is the HOST's decision.
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    result = api.guard(src)
    assert result["ok"] and "def bump(" in result["source"]
    assert list(tmp_path.iterdir()) == [src], "api wrote files unbidden"


def test_repair_reports_a_bad_engine_spec_as_a_value(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    result = api.repair(src, tmp_path / "w", engine="not-an-engine")
    assert result["verified"] is False
    assert "unknown engine" in result["reason"]


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
def test_verify_returns_the_documented_payload(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(GOOD)
    payload = api.verify(src, tmp_path / "w")
    assert payload["status"] == "ok"
    assert payload["schema"] == "veripy-failures/1"
    assert payload["toolchain"]["taxonomy_version"] == \
        api.toolchain_info()["taxonomy_version"]
