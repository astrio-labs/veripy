"""Comment formatting preserves proof enrollment and source positions."""
import shutil
import subprocess

import pytest

from veripy.api import verify
from veripy.backends.dafny.encoder import encode_module
from veripy.frontend.extract import parse_source, spec_comment_sites

SOURCE = '''#@ requires n >= 0
#@ ensures result == n
def count(n: int) -> int:
    total = 0
    for i in range(n):
        #@ invariant total == i
        total += 1
    return total
'''


def test_formatter_space_preserves_contracts_maps_and_proof_sites():
    spaced = SOURCE.replace("#@", "# @")
    original = parse_source(SOURCE)
    formatted = parse_source(spaced)
    assert formatted == original
    left = encode_module(SOURCE, original, "count.py")
    right = encode_module(spaced, formatted, "count.py")
    assert left.dafny_source == right.dafny_source
    assert left.line_map == right.line_map
    hooks = "# @ proof L()\ndef count(n: int) -> int:\n    return n\n"
    assert spec_comment_sites(hooks, "proof") == {1: 0}


def test_comment_marker_inside_string_does_not_enroll_source():
    source = 'text = "# @ ensures False"\ndef count(n: int) -> int:\n    return n\n'
    assert not parse_source(source).functions
    assert not spec_comment_sites(source, "ensures")


@pytest.mark.requires_prover("dafny")
def test_ruff_roundtrip_retains_actual_loop_proof(tmp_path):
    ruff = shutil.which("ruff")
    if ruff is None:
        pytest.skip("ruff is needed for formatter integration")
    module = tmp_path / "count.py"
    module.write_text(SOURCE)
    subprocess.run([ruff, "check", "--isolated", "--select", "E265", "--fix", str(module)], check=True, capture_output=True)
    subprocess.run([ruff, "format", "--isolated", str(module)], check=True, capture_output=True)
    assert "# @ ensures" in module.read_text()
    assert parse_source(module.read_text()).functions
    result = verify(module, tmp_path / "proof", time_limit=10)
    assert result["status"] == "ok", result
