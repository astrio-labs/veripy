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
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

from ..repair import Engine, repair_file


@dataclass
class ExamScore:
    task_id: str
    restored: bool
    iterations: int
    reason: str
    golden_lemmas: list[str] = field(default_factory=list)


def exam_tasks(tasks_root: Path) -> list[Path]:
    """Golden tasks that carry proof additions to strip."""
    return sorted(
        p.parent for p in tasks_root.glob("*/task.proofs.dfy")
    )


def run_repair_exam(tasks_root: Path, workdir: Path,
                    engine_factory: Callable[[], Engine],
                    max_iterations: int = 4, time_limit: int = 60) -> list[ExamScore]:
    from ..backends.dafny.encoder import load_proof_sidecar

    # The workspace must never overlap the corpus: with --tasks pointed at
    # (or inside) the workdir, the per-task cleanup would recursively
    # delete golden sources and sidecars.
    tasks_res, work_res = tasks_root.resolve(), workdir.resolve()
    if tasks_res == work_res or tasks_res in work_res.parents \
            or work_res in tasks_res.parents:
        raise ValueError(
            f"exam workdir {workdir} overlaps the task corpus {tasks_root} — "
            f"choose a workdir outside the corpus")

    scores: list[ExamScore] = []
    for task_dir in exam_tasks(tasks_root):
        task_id = task_dir.name
        exam_dir = workdir / task_id
        if exam_dir.is_symlink():
            # A symlink here could alias corpus data; remove the LINK
            # itself, never what it points at.
            exam_dir.unlink()
        elif exam_dir.exists():
            resolved = exam_dir.resolve()
            if resolved == tasks_res or tasks_res in resolved.parents \
                    or resolved in tasks_res.parents:
                raise ValueError(
                    f"exam workspace {exam_dir} resolves into the task "
                    f"corpus {tasks_root} — refusing to clean it")
            # A rerun must start stripped: a retained workspace proof would
            # score a stale restoration.
            shutil.rmtree(exam_dir)
        exam_dir.mkdir(parents=True)
        stripped = exam_dir / "task.py"
        stripped.write_text((task_dir / "task.py").read_text())
        # No sidecar is copied: that is the exam. Each task gets a FRESH
        # engine so a stateful engine (file:<dir>) replays its own attempt
        # sequence per task instead of continuing a previous task's counter.
        golden = load_proof_sidecar(task_dir / "task.py")
        outcome = repair_file(stripped, exam_dir / "repair", engine_factory(),
                              max_iterations=max_iterations,
                              time_limit=time_limit)
        scores.append(ExamScore(
            task_id=task_id,
            restored=outcome.verified,
            iterations=outcome.iterations,
            reason=outcome.reason,
            golden_lemmas=sorted(golden.lemmas),
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
