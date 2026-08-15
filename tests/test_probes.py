"""The checked-in Dafny probes (docs/probes/) must still verify.

A probe is a hand-written target: the shape the encoder is being built
toward, checked in with a claimed result ("15 verified, 0 errors"). That
claim is evidence only for as long as someone re-runs it — a Dafny upgrade
or an edit to the probe can invalidate it silently, and a stale claim in
docs is worse than no claim, because the slice gets built against it.

Discovery is by glob so a future probe is covered the moment it lands.
"""

import re
from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny, verify_dafny_file

PROBES = Path(__file__).resolve().parent.parent / "docs" / "probes"
FILES = sorted(PROBES.rglob("*.dfy"))


def test_probe_corpus_present():
    # Not skipped on a missing Dafny: an empty glob would leave the
    # parametrized test below with zero cases, which pytest reports as a
    # green run. The denominator gets its own assertion so "nothing was
    # checked" can never read as "everything passed".
    assert FILES, f"no .dfy probes found under {PROBES}"


@pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")
@pytest.mark.parametrize("path", FILES, ids=lambda p: p.stem)
def test_probe_verifies(path):
    result = verify_dafny_file(path, {}, time_limit=60)
    assert result.error is None, result.error
    assert result.ok, [f"{d.dafny_line}: {d.message}" for d in result.diagnostics]
    # `ok` is Dafny's exit status, which a probe containing no proof
    # obligations at all would also earn ("0 verified, 0 errors"). Require
    # the summary to account for at least one discharged obligation.
    counted = re.search(r"(\d+) verified", result.summary)
    assert counted, f"no verification summary in dafny output: {result.raw[:400]}"
    assert int(counted.group(1)) > 0, f"probe proved nothing: {result.summary}"
