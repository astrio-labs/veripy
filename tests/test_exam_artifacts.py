"""Published exam artifacts must still be what the write-up says they are.

`docs/EVALUATION.md` cites engine-written proof packs as evidence for the
proof-repair numbers, and a paper will cite them again. An archived pack
that no longer verifies — because the preamble moved, the task's spec was
strengthened, or the file was edited — would be a false claim sitting in
the repository with a link pointing at it.

The naming convention IS the claim, and both directions are pinned:

    <task>-engine-pack-<tag>.dfy                 -> verifies with that task
    <task>-engine-unverified-attempt-<tag>.dfy   -> must NOT verify

The second direction matters as much as the first: a near-miss that
quietly starts verifying is no longer a near-miss, and the sentence in
EVALUATION.md describing why it failed becomes wrong.
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


def _the_prover_rejected_it(payload: dict) -> bool:
    """Evidence that the prover ran and turned this pack down.

    Not the same as `status != "ok"`: a missing Dafny, a subprocess
    timeout, an unreadable sidecar and a spec that no longer encodes all
    report a non-ok status without ever putting a proof obligation to the
    prover, so `!= "ok"` is satisfied by a toolchain that never worked —
    the archive's negative claim would then be "checked" by nothing. Only
    `failed` means obligations were tried and not discharged, and a
    `failed` carrying no records is a verdict with nothing readable in it.
    """
    return payload["status"] == "failed" and bool(payload["failures"])


def test_the_archive_is_not_empty():
    # A glob that silently matches nothing would make every test below
    # vacuously pass.
    assert _packs("-engine-pack-") and _packs("-engine-unverified-attempt-")


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
@pytest.mark.parametrize("artifact", _packs("-engine-unverified-attempt-"),
                         ids=lambda p: p.name)
def test_archived_near_miss_still_misses(artifact, tmp_path):
    payload = _run(artifact, tmp_path)
    assert _the_prover_rejected_it(payload), (
        f"{artifact.name} is cited as an attempt the prover REJECTED, but "
        f"this run ended as {payload['status']!r} "
        f"({payload.get('error') or payload['failures'] or 'no records'}) — "
        f"either it now verifies and the write-up's explanation of why it "
        f"failed is stale, or nothing was proved here at all")


def test_a_broken_toolchain_is_not_a_near_miss():
    # The check the near-miss test rests on has to be able to fail for the
    # right reason. `status != "ok"` accepted every one of these, so a CI
    # run whose Dafny was missing or timing out would have "confirmed" the
    # archive's negative claim without the prover reading a single line.
    assert not _the_prover_rejected_it(
        {"status": "tool-error", "error": "dafny failed to run",
         "failures": []})
    assert not _the_prover_rejected_it(
        {"status": "encode-error",
         "failures": [{"kind": "conformance", "rule": "unsupported-stmt"}]})
    assert not _the_prover_rejected_it({"status": "failed", "failures": []})
    assert _the_prover_rejected_it(
        {"status": "failed", "failures": [{"kind": "postcondition"}]})


def test_every_artifact_declares_which_way_it_goes():
    # An artifact matching neither convention is tested by nothing.
    known = {p.name for p in _packs("-engine-pack-")}
    known |= {p.name for p in _packs("-engine-unverified-attempt-")}
    for path in ARTIFACTS.glob("*.dfy"):
        assert path.name in known, (
            f"{path.name} follows neither naming convention, so no test "
            f"checks it; name it <task>-engine-pack-<tag>.dfy or "
            f"<task>-engine-unverified-attempt-<tag>.dfy")


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
