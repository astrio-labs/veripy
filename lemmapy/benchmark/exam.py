"""Proof-repair exams (M2, BENCHMARK.md): strip the proof additions from
golden tasks and score their restoration under frozen specs.

An exam variant is the golden task WITHOUT its `.proofs.dfy` sidecar; the
`#@ proof` clauses stay in the (frozen) source, so encoding fails until the
engine supplies a sidecar defining exactly the lemmas those clauses name —
the R4 rung must be re-earned through the same whitelist and prover as the
golden proof. Specs are frozen: the engine can only add proof, never
weaken the property.

Only sidecar-bearing tasks sit the exam: executable proof-hint asserts are
part of the admitted source (they are runtime checks too), and the repair
loop's contract is that the source is frozen.
"""

from __future__ import annotations

import shutil
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from ..repair import Engine, repair_file


@dataclass
class ExamScore:
    task_id: str
    restored: bool
    iterations: int
    reason: str
    golden_lemmas: list[str] = field(default_factory=list)
    # Telemetry for the experiment ledger: per-verify attempt records
    # (from RepairOutcome.attempts), wall-clock for the whole task, and
    # per-engine-call usage (zipped by call order — call order IS attempt
    # order; None when the engine reports no usage).
    attempts: list[dict[str, Any]] = field(default_factory=list)
    wall_ms: int = 0
    usage: list[dict[str, Any] | None] = field(default_factory=list)


def exam_tasks(tasks_root: Path) -> list[Path]:
    """Golden tasks that carry proof additions to strip."""
    return sorted(
        p.parent for p in tasks_root.glob("*/task.proofs.dfy")
    )


# In PROVER_KINDS, but NOT evidence that an obligation went undischarged.
# `resolution` means the sidecar did not typecheck, so — by its own entry in
# lemmapy/failures.py — the proof was never attempted. Reading it as "the
# prover needed the pack" would repeat this screen's original bug one level
# down: a load-bearing verdict drawn from a run that observed nothing about
# provability. The honest verdict for it is `inconclusive`.
NON_EVIDENCE_KINDS = frozenset({"resolution"})


@dataclass
class ScreenResult:
    """Whether a task's proof pack is LOAD-BEARING — i.e. whether an exam
    row over it measures anything."""

    task_id: str
    verdict: str          # "load-bearing" | "vacuous" | "inconclusive" | "broken"
    detail: str
    stripped_status: str | None = None
    prover_kinds: list[str] = field(default_factory=list)

    @property
    def adoptable(self) -> bool:
        return self.verdict == "load-bearing"


def strip_proof_clauses(source: str) -> str:
    """Remove every `#@ proof` clause. The exam keeps them (the engine must
    define exactly the lemmas they name); the SCREEN must not.

    Which lines are clauses is asked of the spec tokenizer, not of a prefix
    match: the parser splits on whitespace after `#@`, so `#@proof L()` and
    `#@  proof L()` are clauses too, and a prefix match that misses one
    leaves it naming a lemma the stripped file no longer has — the encoder
    then rejects the file and the screen reports `inconclusive` for a task
    it could have judged. In the other direction a line-based match deletes
    `#@ proof`-looking text inside a docstring, changing source the screen
    is supposed to leave alone.

    A clause trailing real code (`y = x  #@ proof L()`) loses the comment
    only; deleting its line would delete the statement.
    """
    from ..frontend.extract import spec_comment_sites

    sites = spec_comment_sites(source, "proof")
    kept: list[str] = []
    for n, line in enumerate(source.splitlines(keepends=True), 1):
        col = sites.get(n)
        if col is None:
            kept.append(line)
        elif line[:col].strip():
            kept.append(line[:col].rstrip() + line[len(line.rstrip("\r\n")):])
    return "".join(kept)


def screen_sidecar(task_dir: Path, time_limit: int = 60) -> ScreenResult:
    """Is this task's `.proofs.dfy` doing any work?

    A task Z3 proves from its invariants alone makes an exam row that
    measures nothing, so every roster task must fail WITHOUT its pack. The
    screen has to remove two things, not one:

    - the sidecar, and
    - the `#@ proof` clauses that name its lemmas

    Removing only the sidecar leaves the clauses pointing at lemmas that no
    longer exist, and the ENCODER rejects the file ("unknown lemma 'X'")
    before the prover ever runs. That is a conformance rejection, not
    evidence about provability — it happens for every task, vacuous or not,
    so a screen built on it can never fail and never tells you anything.

    Hence three outcomes, not two. `inconclusive` is the one that matters:
    it is what the old screen was silently reporting as a pass.
    """
    from ..agentio import verify_structured
    from ..failures import PROVER_KINDS

    task_id = task_dir.name
    source = (task_dir / "task.py").read_text()
    sidecar = task_dir / "task.proofs.dfy"
    if not sidecar.is_file():
        return ScreenResult(task_id, "broken", "no task.proofs.dfy to screen")

    with tempfile.TemporaryDirectory() as tmp:
        golden_dir = Path(tmp) / "golden"
        golden_dir.mkdir()
        (golden_dir / "task.py").write_text(source)
        (golden_dir / "task.proofs.dfy").write_text(sidecar.read_text())
        golden = verify_structured(golden_dir / "task.py", golden_dir / "out",
                                   time_limit=time_limit)
        if golden["status"] != "ok":
            return ScreenResult(
                task_id, "broken",
                f"does not verify WITH its pack ({golden['status']}) — fix the "
                f"task before screening it", golden["status"])

        bare_dir = Path(tmp) / "bare"
        bare_dir.mkdir()
        (bare_dir / "task.py").write_text(strip_proof_clauses(source))
        bare = verify_structured(bare_dir / "task.py", bare_dir / "out",
                                 time_limit=time_limit)

    status = bare["status"]
    if status == "ok":
        return ScreenResult(
            task_id, "vacuous",
            "verifies without the pack — an exam row over it measures "
            "nothing, and the pack is dead weight", status)
    kinds = sorted({f.get("kind") for f in (bare.get("failures") or [])
                    if f.get("kind") in PROVER_KINDS})
    evidence = [k for k in kinds if k not in NON_EVIDENCE_KINDS]
    if status != "failed" or not evidence:
        # Name the kinds when there were any: `failed` + `resolution` reads
        # nothing like `encode-error`, and the reader has to know which.
        observed = ", ".join(kinds) or status
        return ScreenResult(
            task_id, "inconclusive",
            f"stripping the pack left the file un-provable for a NON-proof "
            f"reason ({observed}); the screen observed nothing about "
            f"provability", status)
    return ScreenResult(
        task_id, "load-bearing",
        f"without the pack the prover reports {', '.join(evidence)}",
        status, evidence)


def render_screen_report(results: list[ScreenResult]) -> str:
    if not results:
        return "no sidecar-bearing tasks to screen"
    width = max(len(r.task_id) for r in results)
    lines = [f"{'task'.ljust(width)}  verdict        detail",
             "-" * (width + 60)]
    for r in results:
        lines.append(f"{r.task_id.ljust(width)}  {r.verdict:<14} {r.detail}")
    bad = [r for r in results if not r.adoptable]
    lines.append("-" * (width + 60))
    lines.append(f"load-bearing: {len(results) - len(bad)}/{len(results)}")
    return "\n".join(lines)


def check_workdir_disjoint(tasks_root: Path, workdir: Path) -> Path:
    """The workspace must never overlap the corpus: with --tasks pointed at
    (or inside) the workdir, the per-task cleanup would recursively delete
    golden sources and sidecars. Returns the resolved corpus root."""
    tasks_res, work_res = tasks_root.resolve(), workdir.resolve()
    if tasks_res == work_res or tasks_res in work_res.parents \
            or work_res in tasks_res.parents:
        raise ValueError(
            f"exam workdir {workdir} overlaps the task corpus {tasks_root} — "
            f"choose a workdir outside the corpus")
    return tasks_res


def prepare_exam_workspace(tasks_root: Path, workdir: Path,
                           task_id: str) -> Path:
    """A clean `<workdir>/<task_id>/`, refusing anything that could reach
    the corpus. Shared by every exam: a rerun must start stripped (a
    retained workspace proof would score a stale restoration), and no
    cleanup may ever follow a link into the golden corpus."""
    tasks_res = check_workdir_disjoint(tasks_root, workdir)
    exam_dir = workdir / task_id
    if exam_dir.is_symlink():
        # A symlink here could alias corpus data; remove the LINK itself,
        # never what it points at.
        exam_dir.unlink()
    elif exam_dir.exists():
        resolved = exam_dir.resolve()
        if resolved == tasks_res or tasks_res in resolved.parents \
                or resolved in tasks_res.parents:
            raise ValueError(
                f"exam workspace {exam_dir} resolves into the task corpus "
                f"{tasks_root} — refusing to clean it")
        shutil.rmtree(exam_dir)
    exam_dir.mkdir(parents=True)
    return exam_dir


def run_repair_exam(tasks_root: Path, workdir: Path,
                    engine_factory: Callable[[], Engine],
                    max_iterations: int = 4, time_limit: int = 60,
                    only: set[str] | None = None) -> list[ExamScore]:
    from ..backends.dafny.encoder import load_proof_sidecar

    check_workdir_disjoint(tasks_root, workdir)
    scores: list[ExamScore] = []
    for task_dir in exam_tasks(tasks_root):
        task_id = task_dir.name
        if only is not None and task_id not in only:
            continue
        exam_dir = prepare_exam_workspace(tasks_root, workdir, task_id)
        stripped = exam_dir / "task.py"
        stripped.write_text((task_dir / "task.py").read_text())
        # No sidecar is copied: that is the exam. Each task gets a FRESH
        # engine so a stateful engine (file:<dir>) replays its own attempt
        # sequence per task instead of continuing a previous task's counter
        # (and so per-call usage attributes cleanly to one task).
        golden = load_proof_sidecar(task_dir / "task.py")
        engine = engine_factory()
        t0 = time.monotonic()
        outcome = repair_file(stripped, exam_dir / "repair", engine,
                              max_iterations=max_iterations,
                              time_limit=time_limit)
        scores.append(ExamScore(
            task_id=task_id,
            restored=outcome.verified,
            iterations=outcome.iterations,
            reason=outcome.reason,
            golden_lemmas=sorted(golden.lemmas),
            attempts=outcome.attempts,
            wall_ms=int((time.monotonic() - t0) * 1000),
            usage=list(getattr(engine, "usage_log", [])),
        ))
    return scores


def render_exam_report(scores: list[ExamScore]) -> str:
    if not scores:
        return "proof-repair exam: no sidecar-bearing tasks to examine"
    lines = [f"{'task':<22} restored  iterations  golden-lemmas"]
    lines.append("-" * len(lines[0]))
    for s in scores:
        mark = "yes" if s.restored else f"NO ({s.reason})"
        lines.append(f"{s.task_id:<22} {mark:<9} {s.iterations:<11} "
                     f"{len(s.golden_lemmas)}")
    restored = sum(1 for s in scores if s.restored)
    lines.append("-" * len(lines[0]))
    lines.append(f"restored: {restored}/{len(scores)}")
    return "\n".join(lines)
