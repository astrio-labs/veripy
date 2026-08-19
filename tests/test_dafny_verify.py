"""End-to-end `veripy verify` integration tests (need dafny on PATH)."""

from pathlib import Path

import pytest

from veripy.backends.dafny.driver import find_dafny
from veripy.cli import cmd_verify

pytestmark = pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")

REPO = Path(__file__).resolve().parent.parent
EXAMPLES = REPO / "examples"

FIXED_CLAMP = (
    "#@ verified\n"
    "#@ requires lo <= hi\n"
    "#@ ensures lo <= result <= hi\n"
    "#@ ensures result == x or result == lo or result == hi\n"
    "def clamp(x: int, lo: int, hi: int) -> int:\n"
    "    return min(max(x, lo), hi)\n"
)


def test_bump_verifies(tmp_path, capsys):
    assert cmd_verify([EXAMPLES / "bump.py"], tmp_path, time_limit=30) == 0
    assert "VERIFIED" in capsys.readouterr().out


def test_seeded_clamp_bug_fails_statically(tmp_path, capsys):
    status = cmd_verify([EXAMPLES / "clamp.py"], tmp_path, time_limit=30)
    out = capsys.readouterr().out
    assert status == 1
    assert "VERIFICATION FAILED" in out
    assert "clamp.py:9" in out  # mapped back to the Python return line


def test_fixed_clamp_verifies(tmp_path, capsys):
    src = tmp_path / "clamp_fixed.py"
    src.write_text(FIXED_CLAMP)
    assert cmd_verify([src], tmp_path / "out", time_limit=30) == 0
    assert "VERIFIED" in capsys.readouterr().out


def test_gcd_verifies_with_proof_additions(tmp_path, capsys):
    # The designated proof-additions case: #@ proof clause + lemma sidecar.
    status = cmd_verify(
        [EXAMPLES / "contact" / "he_humaneval_13.py"], tmp_path,
        time_limit=60, types=False,
    )
    assert status == 0
    assert "greatest_common_divisor" in capsys.readouterr().out


def test_contact_below_threshold_verifies(tmp_path, capsys):
    status = cmd_verify(
        [EXAMPLES / "contact" / "he_humaneval_52.py"], tmp_path, time_limit=30
    )
    assert status == 0
    assert "below_threshold" in capsys.readouterr().out


def test_below_zero_verifies_with_sum_fold(tmp_path, capsys):
    # Slice 6: sum() over a growing prefix, stepped by an executable assert.
    status = cmd_verify(
        [EXAMPLES / "contact" / "he_humaneval_3.py"], tmp_path,
        time_limit=60, types=False,
    )
    assert status == 0
    assert "below_zero" in capsys.readouterr().out


def test_sum_of_squares_verifies_with_genexp_fold(tmp_path, capsys):
    status = cmd_verify(
        [EXAMPLES / "contact" / "mbpp_sum_squares.py"], tmp_path,
        time_limit=60, types=False,
    )
    assert status == 0
    assert "sum_of_squares" in capsys.readouterr().out


NEG_INDEX = (
    "#@ verified\n"
    "#@ requires len(l) > 0\n"
    "#@ ensures result == l[len(l) - 1]\n"
    "def last(l: list[int]) -> int:\n"
    "    return l[-1]\n"
)


def test_negative_indexing_verifies_python_exactly(tmp_path, capsys):
    src = tmp_path / "last.py"
    src.write_text(NEG_INDEX)
    status = cmd_verify([src], tmp_path / "out", time_limit=30, types=False)
    assert status == 0
    assert "VERIFIED" in capsys.readouterr().out


def test_preamble_outcome_supports_raising_and_propagation(tmp_path):
    # The preamble's PyOutcome must be FAILURE-COMPATIBLE — `:-` only
    # resolves when IsFailure/PropagateFailure/Extract are members of the
    # datatype. A free-function version type-checks as ordinary Dafny and
    # then fails at every `:-` site, so this pins the shape, not just the
    # presence of the names.
    import subprocess

    from veripy.backends.dafny.driver import find_dafny
    from veripy.backends.dafny.preamble import PREAMBLE

    dafny = find_dafny()
    if dafny is None:
        pytest.skip("dafny not installed")
    stub = tmp_path / "outcome.dfy"
    stub.write_text(PREAMBLE + """
method checked_div(a: int, b: int) returns (result: PyOutcome<int>)
  ensures b == 0 ==> result == PyErr(ZeroDivisionError)
  ensures b != 0 ==> result == PyOk(PyFloorDiv(a, b))
{
  if b == 0 { return PyErr(ZeroDivisionError); }
  return PyOk(PyFloorDiv(a, b));
}

method propagates(a: int, b: int, c: int) returns (result: PyOutcome<int>)
  ensures b != 0 && c != 0 ==> result == PyOk(PyFloorDiv(a, b) + PyFloorDiv(a, c))
  ensures b == 0 || c == 0 ==> result.PyErr?
{
  var x :- checked_div(a, b);
  var y :- checked_div(a, c);
  return PyOk(x + y);
}

method handles(a: int, b: int, fallback: int) returns (result: int)
  ensures b == 0 ==> result == fallback
  ensures b != 0 ==> result == PyFloorDiv(a, b)
{
  var o := checked_div(a, b);
  match o {
    case PyErr(e) => return fallback;
    case PyOk(v) => return v;
  }
}
""")
    proc = subprocess.run([dafny, "verify", "--verification-time-limit", "60",
                           str(stub)], capture_output=True, text=True, timeout=600)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "0 errors" in proc.stdout


BAD_PACK_SRC = (
    "#@ ensures result == x\n"
    "def f(x: int) -> int:\n"
    "    #@ proof Bogus(x)\n"
    "    return x\n"
)
# Has a body, so it clears the whitelist (a bodiless lemma is an axiom and
# is rejected); the body simply cannot prove the ensures.
BAD_PACK = "lemma Bogus(x: int)\n  ensures x != x\n{\n}\n"


def test_sidecar_failure_names_the_sidecar_not_a_python_line(tmp_path, capsys):
    # The driver maps every Dafny line back through the line map, so a
    # failure in the APPENDED sidecar region came out as `f.py:<line>` --
    # a line that has nothing to do with the failing lemma, sending the
    # reader to the wrong file. The structured payload always said
    # `region: "sidecar"`; the printed line disagreed with it.
    src = tmp_path / "f.py"
    src.write_text(BAD_PACK_SRC)
    (tmp_path / "f.proofs.dfy").write_text(BAD_PACK)
    assert cmd_verify([src], tmp_path / "out", time_limit=30, types=False) == 1
    out = capsys.readouterr().out
    assert "f.proofs.dfy:" in out
    assert "f.py:" not in out.replace(str(src), "")  # only the header names f.py


def test_sidecar_line_is_the_files_own_line(tmp_path, capsys):
    # Not merely "some line in the sidecar": the number must index the file
    # the reader opens, past the generated header the stub prepends.
    src = tmp_path / "g.py"
    src.write_text(BAD_PACK_SRC.replace("Bogus", "Deep"))
    pack = ("lemma Filler(x: int)\n  ensures x == x\n{\n}\n\n"
            "lemma Deep(x: int)\n  ensures x != x\n{\n}\n")
    (tmp_path / "g.proofs.dfy").write_text(pack)
    cmd_verify([src], tmp_path / "out", time_limit=30, types=False)
    out = capsys.readouterr().out
    reported = [int(part.split(":")[0])
                for part in out.split("g.proofs.dfy:")[1:]]
    assert reported, out
    lines = pack.split("\n")
    # Every reported line lands inside `Deep`, which starts at line 6.
    assert all(6 <= n <= len(lines) for n in reported), (reported, out)
    assert any("Deep" in lines[n - 1] or "x != x" in lines[n - 1] or
               lines[n - 1].strip() in ("{", "}") for n in reported), out


def test_a_sidecar_failure_gains_no_related_python_line(tmp_path, capsys):
    # Dafny's "Related location" was folded in through the same nearest-above
    # line map, so a related location inside the SIDECAR resolved to whichever
    # Python statement happened to be encoded last -- pointing the reader at a
    # `return` that has nothing to do with the lemma. The primary location was
    # fixed first; this is the same fabrication one layer down, in the message.
    src = tmp_path / "f.py"
    src.write_text(BAD_PACK_SRC)
    (tmp_path / "f.proofs.dfy").write_text(BAD_PACK)
    cmd_verify([src], tmp_path / "out", time_limit=30, types=False)
    out = capsys.readouterr().out
    assert "f.proofs.dfy:" in out
    assert "related: source line" not in out


def test_a_source_failure_keeps_its_related_clause(tmp_path, capsys):
    # The control: the fold exists so a postcondition failure points at the
    # `ensures` clause and not only at the return path. Bounding the map must
    # not cost that.
    src = tmp_path / "g.py"
    src.write_text("#@ ensures result == x + 1\ndef g(x: int) -> int:\n    return x\n")
    cmd_verify([src], tmp_path / "out", time_limit=30, types=False)
    out = capsys.readouterr().out
    assert "g.py:3" in out and "related: source line 1" in out


def test_isqrt_maximality_verifies_without_proof_additions(tmp_path, capsys):
    # The counterpoint to gcd: the SAME maximality shape ("no k in range
    # beats the answer"), but squaring's monotonicity on non-negatives is
    # within Z3's reach where divisibility was not — so this one needs no
    # sidecar. Worth pinning: if it ever starts needing one, the fragment's
    # nonlinear reach has regressed.
    #
    # The no-sidecar half has to be asserted, not assumed: cmd_verify loads
    # `<stem>.proofs.dfy` silently whenever it exists, so dropping proof
    # additions beside isqrt.py would leave a success-only test green while
    # destroying the very contrast it is here to record.
    assert not (EXAMPLES / "isqrt.proofs.dfy").exists()
    status = cmd_verify([EXAMPLES / "isqrt.py"], tmp_path, time_limit=60,
                        types=False)
    assert status == 0
    assert "VERIFIED (isqrt)" in capsys.readouterr().out
