"""`lemmapy check` fragment conformance: the encoder dry-run is the
conformance authority — check reports exactly what verify would reject,
without needing Dafny installed."""

from pathlib import Path

from lemmapy.cli import cmd_check

CONFORMANT = (
    "#@ ensures result == x + 1\n"
    "def bump(x: int) -> int:\n"
    "    return x + 1\n"
)

OUTSIDE = (
    "#@ ensures result >= 0\n"
    "def f(xs: list[int]) -> int:\n"
    "    return len(set(xs))\n"
)

SHADOWING = (
    "sum = 5\n"
    "#@ ensures result == 0\n"
    "def f() -> int:\n"
    "    return 0\n"
)


def _check(tmp_path: Path, source: str, **kw) -> tuple[int, str]:
    src = tmp_path / "m.py"
    src.write_text(source)
    import contextlib
    import io

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        status = cmd_check([src], types=False, **kw)
    return status, buf.getvalue()


def test_conformant_module_passes(tmp_path):
    status, out = _check(tmp_path, CONFORMANT)
    assert status == 0
    assert "fragment: conformant (bump)" in out


def test_outside_fragment_reported_with_line(tmp_path):
    status, out = _check(tmp_path, OUTSIDE)
    assert status == 1
    assert "fragment:" in out and "m.py:3" in out


def test_builtin_shadowing_caught_by_check(tmp_path):
    status, out = _check(tmp_path, SHADOWING)
    assert status == 1
    assert "shadows a builtin" in out


def test_no_fragment_opt_out(tmp_path):
    status, out = _check(tmp_path, OUTSIDE, fragment=False)
    assert status == 0
    assert "fragment:" not in out


def test_unspecced_module_skips_fragment(tmp_path):
    status, out = _check(tmp_path, "def f() -> int:\n    return 0\n")
    assert status == 0
    assert "fragment:" not in out


def test_undecodable_sidecar_is_a_controlled_failure(tmp_path):
    # Invalid UTF-8 in the sidecar must be a check failure, not a traceback.
    src = tmp_path / "m.py"
    src.write_text(CONFORMANT)
    (tmp_path / "m.proofs.dfy").write_bytes(b"\xff\xfelemma {")
    import contextlib
    import io

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        status = cmd_check([src], types=False)
    assert status == 1
    assert "unreadable proof sidecar" in buf.getvalue()


def test_broken_sidecar_reported_by_check(tmp_path):
    src = tmp_path / "m.py"
    src.write_text(CONFORMANT)
    (tmp_path / "m.proofs.dfy").write_text("lemma Bad(x: int)\n  ensures x == x\n")
    import contextlib
    import io

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        status = cmd_check([src], types=False)
    assert status == 1
    assert "axiom" in buf.getvalue()


def test_check_names_in_fragment_candidates(tmp_path):
    # A feedback-sufficiency run found that `check` on an unannotated
    # in-fragment file said only "(no #@ specs found)" — no signal that the
    # file was even a candidate, and no hint what to write next. The
    # actionable half is computable, so it should be said.
    status, out = _check(tmp_path, (
        "def count_evens(xs: list[int]) -> int:\n"
        "    total = 0\n"
        "    for i in range(len(xs)):\n"
        "        if xs[i] % 2 == 0:\n"
        "            total = total + 1\n"
        "    return total\n"
        "\n"
        "\n"
        "def uses_a_set(xs: list[int]) -> int:\n"
        "    return len(set(xs))\n"
    ))
    assert status == 0
    assert "in-fragment and ready to annotate: count_evens" in out
    # The out-of-fragment function must NOT be advertised: sending someone
    # to annotate a function the encoder will reject is worse than silence.
    assert "uses_a_set" not in out
    assert "#@ ensures" in out  # says what to write, not just which


def test_decorated_function_is_not_advertised_as_a_candidate(tmp_path):
    # The encoder probe never looks at the decorator list, so a decorated
    # function used to be listed as in-fragment. It is not (X-DECOR: the
    # decorator replaces the function object), and the printed advice was
    # wrong for it twice over: a contract block attaches above the FIRST
    # DECORATOR, so "directly above `def`" produces an orphan, not a spec.
    status, out = _check(tmp_path, (
        "import functools\n"
        "\n"
        "\n"
        "@functools.cache\n"
        "def double(x: int) -> int:\n"
        "    return x * 2\n"
    ))
    assert status == 0
    assert "double" not in out
    assert "ready to annotate" not in out


def test_check_stays_quiet_when_nothing_is_a_candidate(tmp_path):
    status, out = _check(tmp_path, (
        "def uses_a_set(xs: list[int]) -> int:\n"
        "    return len(set(xs))\n"
    ))
    assert status == 0
    assert "(no #@ specs found)" in out
    assert "ready to annotate" not in out
