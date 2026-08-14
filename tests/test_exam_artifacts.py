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

from pathlib import Path

import pytest

from lemmapy.agentio import verify_structured
from lemmapy.backends.dafny.driver import find_dafny

REPO = Path(__file__).resolve().parent.parent
ARTIFACTS = REPO / "docs" / "exam-artifacts"
TASKS = REPO / "benchmark" / "tasks"

pytestmark = pytest.mark.skipif(find_dafny() is None, reason="dafny not installed")


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


def test_the_archive_is_not_empty():
    # A glob that silently matches nothing would make every test below
    # vacuously pass.
    assert _packs("-engine-pack-") and _packs("-engine-unverified-attempt-")


@pytest.mark.parametrize("artifact", _packs("-engine-pack-"),
                         ids=lambda p: p.name)
def test_archived_engine_pack_still_verifies(artifact, tmp_path):
    payload = _run(artifact, tmp_path)
    assert payload["status"] == "ok", (
        f"{artifact.name} is cited as a restored pack but no longer "
        f"verifies against benchmark/tasks/{_task_of(artifact)}: "
        f"{payload.get('failures') or payload.get('error')}")


@pytest.mark.parametrize("artifact", _packs("-engine-unverified-attempt-"),
                         ids=lambda p: p.name)
def test_archived_near_miss_still_misses(artifact, tmp_path):
    payload = _run(artifact, tmp_path)
    assert payload["status"] != "ok", (
        f"{artifact.name} is cited as an attempt that did NOT verify, but "
        f"it now does — the write-up's explanation of why it failed is "
        f"stale")


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
