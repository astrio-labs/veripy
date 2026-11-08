"""Handwritten examples exercise reusable translation, actual execution and faults."""

from datetime import timedelta
from pathlib import Path
import runpy

import pytest

from veripy.api import verify

EXAMPLES = Path(__file__).resolve().parents[2] / "examples/source_contracts"


def test_examples_execute_as_ordinary_python():
    pure = runpy.run_path(str(EXAMPLES / "measurements.py"))
    bounds = pure["Interval"](-2, 5)
    assert pure["contains"](bounds, -2)
    assert not pure["contains"](bounds, 6)
    samples = [-20, 0, 30]
    assert pure["clip_readings"](samples, -2, 5) == [-2, 0, 5]
    assert samples == [-20, 0, 30]
    assert pure["advance"](9, 7, -2) == -5
    assert pure["advance"](9, 0, -2) == 9
    pauses = runpy.run_path(str(EXAMPLES / "pauses.py"))
    window = pauses["RetryWindow"](timedelta(seconds=2), timedelta(seconds=3))
    assert window.pause(0) == timedelta(seconds=2)
    assert window.pause(1) == window.pause(100) == timedelta(seconds=3)
    for base, cap in [
        (timedelta(microseconds=1), timedelta.max),
        (timedelta.max, timedelta.max),
    ]:
        expected = min(base * 2, cap) if base < timedelta.max else cap
        assert pauses["RetryWindow"](base, cap).pause(2) == expected
    with pytest.raises(ValueError):
        window.pause(-1)


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "filename,backend,old,new,expected",
    [
        ("measurements.py", "dafny", "", "", "ok"),
        ("measurements.py", "dafny", "value += stride", "value = value + stride", "ok"),
        (
            "measurements.py",
            "dafny",
            "value += stride",
            "value += stride + 1",
            "failed",
        ),
        (
            "measurements.py",
            "dafny",
            "return [min(max(sample, lower), upper)",
            "return [max(max(sample, lower), upper)",
            "failed",
        ),
        (
            "measurements.py",
            "dafny",
            "return bounds.lower <= point <= bounds.upper",
            "return bounds.lower < point <= bounds.upper",
            "failed",
        ),
        ("pauses.py", "dafny-native", "", "", "ok"),
        (
            "pauses.py",
            "dafny-native",
            "self.cap // self.base < 2",
            "2 > self.cap // self.base",
            "ok",
        ),
        (
            "pauses.py",
            "dafny-native",
            "return self.base * 2",
            "return self.base",
            "failed",
        ),
        (
            "pauses.py",
            "dafny-native",
            "self.cap // self.base < 2",
            "self.cap // self.base < 1",
            "failed",
        ),
    ],
)
def test_fresh_source_proofs_and_meaningful_mutants(
    tmp_path, filename, backend, old, new, expected
):
    source = (EXAMPLES / filename).read_text()
    if old:
        assert old in source
        source = source.replace(old, new)
    module = tmp_path / filename
    module.write_text(source)
    sidecar = (EXAMPLES / filename).with_suffix(".proofs.dfy")
    if sidecar.exists():
        module.with_suffix(".proofs.dfy").write_bytes(sidecar.read_bytes())
    result = verify(
        module, tmp_path / "proof", backend=backend, time_limit=15, keep_artifacts=True
    )
    assert result["status"] == expected, result
    if expected == "failed":
        assert result["failures"]
        assert all(
            f["kind"] in {"postcondition", "invariant", "assertion"}
            for f in result["failures"]
        ), result
