"""End-to-end `lemmapy verify` integration tests (need dafny on PATH)."""

from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.cli import cmd_verify

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


def test_isqrt_maximality_verifies_without_proof_additions(tmp_path, capsys):
    # The counterpoint to gcd: the SAME maximality shape ("no k in range
    # beats the answer"), but squaring's monotonicity on non-negatives is
    # within Z3's reach where divisibility was not — so this one needs no
    # sidecar. Worth pinning: if it ever starts needing one, the fragment's
    # nonlinear reach has regressed.
    status = cmd_verify([EXAMPLES / "isqrt.py"], tmp_path, time_limit=60,
                        types=False)
    assert status == 0
    assert "isqrt" in capsys.readouterr().out
