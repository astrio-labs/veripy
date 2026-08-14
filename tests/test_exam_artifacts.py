"""Published exam artifacts must still be what the write-up says they are.

`docs/EVALUATION.md` cites engine-written proof packs as evidence for the
proof-repair numbers, and a paper will cite them again. An archived pack
that no longer verifies — because the preamble moved, the task's spec was
strengthened, or the file was edited — would be a false claim sitting in
the repository with a link pointing at it.

The naming convention IS the claim, and both directions are pinned:

    <task>-engine-pack-<tag>.dfy                    -> verifies with that task
    <task>-engine-unverified-attempt-<tag>.dfy      -> the prover DISPROVED it
    <task>-engine-inconclusive-attempt-<tag>.dfy    -> the prover ran out of time

The second direction matters as much as the first: a near-miss that
quietly starts verifying is no longer a near-miss, and the sentence in
EVALUATION.md describing why it failed becomes wrong.

The third bucket exists because "did not verify" is not one claim. A pack
whose postcondition the prover DISPROVED and a pack the prover simply
never finished are different facts, and the write-up says different things
about them — so a timeout must not be allowed to stand in for a
disproof, in either direction.
"""

import os
import subprocess
import sys
from pathlib import Path

import pytest

from lemmapy.agentio import verify_structured
from lemmapy.backends.dafny.driver import find_dafny

REPO = Path(__file__).resolve().parent.parent
ARTIFACTS = REPO / "docs" / "exam-artifacts"
TASKS = REPO / "benchmark" / "tasks"

# Only the two tests that run the prover need it. A module-level skip would
# also switch off the filesystem checks below — archive non-empty, naming
# convention, artifact names a real task — so a Dafny-free CI tier would
# report green on an emptied archive or a misnamed artifact.
needs_dafny = pytest.mark.skipif(find_dafny() is None,
                                 reason="dafny not installed")


def _packs(marker: str) -> list[Path]:
    return sorted(p for p in ARTIFACTS.glob(f"*{marker}*.dfy"))


def _task_of(artifact: Path) -> str:
    """`modp-engine-pack-2026-08c.dfy` -> `modp` (task ids contain `_`,
    never `-engine-`, so this split is unambiguous)."""
    return artifact.name.split("-engine-")[0]


def _run(artifact: Path, tmp_path: Path) -> dict:
    task = _task_of(artifact)
    src = tmp_path / f"{task}.py"
    src.write_text((TASKS / task / "task.py").read_text())
    (tmp_path / f"{task}.proofs.dfy").write_text(artifact.read_text())
    return verify_structured(src, tmp_path / "out", time_limit=60)


# In PROVER_KINDS, but NOT evidence that an obligation was DISPROVED.
# `resolution`: the sidecar did not typecheck, so — by its own entry in
# lemmapy/failures.py — the proof was never attempted.
# `timeout`: that entry is explicit that it is "NOT a disproof: the property
# may still hold". A pack the prover never finished has not been turned
# down by it.
_NOT_A_DISPROOF = frozenset({"resolution", "timeout"})


def _prover_verdict(payload: dict) -> str:
    """What an archived attempt's run actually establishes.

    "did not verify" is not one claim, and every weaker way of satisfying it
    has at some point been accepted as if it were the strong one:

    - `status != "ok"` alone is satisfied by a missing Dafny, a subprocess
      failure, or a spec that no longer encodes — a toolchain that never
      worked would have "checked" the archive's negative claim.
    - a `failed` run with no records is a verdict with nothing readable in
      it.
    - `resolution` means the sidecar did not typecheck: no obligation ever
      reached the prover.
    - `timeout` means the prover never finished. That is a real fact about
      the attempt, and it is what `is_prime`'s archived attempt produces —
      but it is not a disproof, and the write-up must not claim one.

    Returns "disproved", "timeout", or "" (nothing established).
    """
    if payload["status"] != "failed":
        return ""
    kinds = {f.get("kind") for f in (payload.get("failures") or [])}
    if kinds - _NOT_A_DISPROOF:
        return "disproved"
    return "timeout" if "timeout" in kinds else ""


# Every recognised suffix, and the verdict its bucket asserts.
_BUCKETS = {
    "-engine-unverified-attempt-": "disproved",
    "-engine-inconclusive-attempt-": "timeout",
}


def test_the_archive_is_not_empty():
    # A glob that silently matches nothing would make every test below
    # vacuously pass.
    assert _packs("-engine-pack-")
    assert all(_packs(marker) for marker in _BUCKETS)


@needs_dafny
@pytest.mark.parametrize("artifact", _packs("-engine-pack-"),
                         ids=lambda p: p.name)
def test_archived_engine_pack_still_verifies(artifact, tmp_path):
    payload = _run(artifact, tmp_path)
    assert payload["status"] == "ok", (
        f"{artifact.name} is cited as a restored pack but no longer "
        f"verifies against benchmark/tasks/{_task_of(artifact)}: "
        f"{payload.get('failures') or payload.get('error')}")


@needs_dafny
@pytest.mark.parametrize(
    "artifact,expected",
    [(p, verdict) for marker, verdict in _BUCKETS.items()
     for p in _packs(marker)],
    ids=lambda x: x.name if hasattr(x, "name") else x)
def test_archived_near_miss_still_misses_the_SAME_way(artifact, expected,
                                                      tmp_path):
    # Not merely "still fails": still fails for the reason its name and the
    # write-up claim. An attempt that drifts from disproved to timed out (or
    # back) makes the sentence describing it wrong, which is the thing this
    # archive exists to keep true.
    payload = _run(artifact, tmp_path)
    assert _prover_verdict(payload) == expected, (
        f"{artifact.name} is cited as an attempt the prover ended by "
        f"{expected!r}, but this run ended as {payload['status']!r} "
        f"({payload.get('error') or payload['failures'] or 'no records'}) — "
        f"either it now verifies and the write-up's explanation of why it "
        f"failed is stale, or nothing was proved here at all")


def test_every_artifact_declares_which_way_it_goes():
    # An artifact matching neither convention is tested by nothing.
    known = {p.name for p in _packs("-engine-pack-")}
    for marker in _BUCKETS:
        known |= {p.name for p in _packs(marker)}
    for path in ARTIFACTS.glob("*.dfy"):
        assert path.name in known, (
            f"{path.name} follows neither naming convention, so no test "
            f"checks it; name it <task>-engine-pack-<tag>.dfy, or "
            f"<task>-engine-<bucket>-attempt-<tag>.dfy with <bucket> one "
            f"of {sorted(m.split('-')[2] for m in _BUCKETS)}")


@pytest.mark.parametrize("artifact", sorted(ARTIFACTS.glob("*.dfy")),
                         ids=lambda p: p.name)
def test_artifact_names_a_real_corpus_task(artifact):
    assert (TASKS / _task_of(artifact) / "task.py").is_file(), (
        f"{artifact.name} names task '{_task_of(artifact)}', which is not "
        f"in benchmark/tasks — the artifact cannot be checked against "
        f"anything")


def test_the_structural_checks_survive_a_prover_free_tier(tmp_path):
    """Re-run the filesystem-only checks the way a CI tier without Dafny
    would see them: an empty PATH, so `find_dafny()` is None.

    A skip is indistinguishable from a pass in the summary line, so a
    module-level skip put these checks — the only ones that would notice an
    emptied archive or an artifact named after no task — permanently out of
    reach of the tier that runs everywhere.
    """
    checks = ["test_the_archive_is_not_empty",
              "test_every_artifact_declares_which_way_it_goes",
              "test_artifact_names_a_real_corpus_task"]
    here = Path(__file__).resolve().relative_to(REPO)
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
         *(f"{here}::{name}" for name in checks)],
        cwd=REPO, capture_output=True, text=True,
        env={**os.environ, "PATH": str(tmp_path)})
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "skipped" not in proc.stdout, (
        "the archive's structural checks are skipped when Dafny is absent, "
        f"so a prover-free CI tier checks nothing:\n{proc.stdout}")


@pytest.mark.parametrize("payload,verdict", [
    # The prover ran and could not discharge an obligation.
    ({"status": "failed", "failures": [{"kind": "postcondition"}]}, "disproved"),
    ({"status": "failed", "failures": [{"kind": "assertion"}]}, "disproved"),
    # The prover never finished. A real fact about the attempt, but the
    # taxonomy is explicit that it is NOT a disproof.
    ({"status": "failed", "failures": [{"kind": "timeout"}]}, "timeout"),
    # Mixed: something was genuinely disproved alongside the noise.
    ({"status": "failed",
      "failures": [{"kind": "timeout"}, {"kind": "postcondition"}]}, "disproved"),
    ({"status": "failed",
      "failures": [{"kind": "resolution"}, {"kind": "assertion"}]}, "disproved"),
    # The sidecar did not typecheck: nothing reached the prover.
    ({"status": "failed", "failures": [{"kind": "resolution"}]}, ""),
    # A toolchain that never worked must not "confirm" anything.
    ({"status": "tool-error", "failures": []}, ""),
    ({"status": "encode-error", "failures": [{"kind": "conformance"}]}, ""),
    # A verdict with nothing readable in it.
    ({"status": "failed", "failures": []}, ""),
    ({"status": "ok", "failures": []}, ""),
])
def test_what_a_run_actually_establishes(payload, verdict):
    # Every row below "disproved" was, at some point in this PR's history,
    # accepted as evidence that the prover turned an archived pack down.
    assert _prover_verdict(payload) == verdict
