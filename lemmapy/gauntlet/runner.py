"""The Gauntlet: LemmaPy's native benchmark runner.

A task is one annotated-Python module (`task.py`, optionally with a
`task.proofs.dfy` lemma sidecar). Every task is scored on the ASSURANCE
LADDER — how far the toolchain can push it:

  R0 gate     specs parse; basedpyright strict is clean
  R1 hunt     CrossHair finds no counterexample against the specs
  R2 mutants  the spec panel: auto-generated single-fault mutants must be
              REFUTED by CrossHair — kill rate measures SPEC STRENGTH,
              a dimension no skeleton-completion benchmark has
  R3 encode   the fragment encoder accepts the module
  R4 prove    Dafny verifies (proof additions allowed: executable asserts,
              `#@ proof` clauses, sidecar lemmas — specs are frozen)
  R5 fidelity Dafny-compiled model agrees with CPython under Hypothesis

The unit being annotated Python (not prover-IR skeletons) means the
benchmark exercises the *product claim* end to end, auto-upgrades as the
fragment grows, and derives task families for free: strip the specs for a
spec-writing exam, strip the proof additions for a proof-repair exam, ship
a surviving mutant for a debugging exam.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

from ..backends.dafny.driver import find_dafny, verify_dafny_file
from ..backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar
from ..backends.runtime.emit import emit_checked
from ..frontend.extract import parse_source
from ..frontend.typegate import run_type_gate
from .mutate import generate_mutations

PASS, FAIL, ERROR, SKIP = "pass", "fail", "error", "skip"


@dataclass
class Rung:
    name: str
    status: str
    detail: str = ""


@dataclass
class TaskScore:
    task_id: str
    rungs: list[Rung] = field(default_factory=list)
    mutants_total: int = 0
    mutants_killed: int = 0
    survivors: list[str] = field(default_factory=list)
    adjudicated: int = 0  # mutants ruled equivalent in meta.json, excluded

    @property
    def height(self) -> int:
        h = 0
        for rung in self.rungs:
            if rung.status in (PASS, SKIP):  # a skipped rung doesn't block the climb
                h += 1
            else:
                break
        return h


def _find_crosshair() -> str | None:
    exe = shutil.which("crosshair")
    if exe:
        return exe
    candidate = Path(sys.executable).parent / "crosshair"
    return str(candidate) if candidate.exists() else None


def _hunt(source: str, name: str, workdir: Path, per_condition_timeout: int) -> tuple[str, str]:
    """Emit runtime contracts and let CrossHair hunt. Returns (verdict, detail)
    with verdict one of: 'clean', 'counterexample', 'error'."""
    exe = _find_crosshair()
    if exe is None:
        return ERROR, "crosshair not installed"
    specs = parse_source(source)
    if specs.errors or specs.orphans:
        return ERROR, "spec errors"
    checked = workdir / f"{name}_checked.py"
    checked.parent.mkdir(parents=True, exist_ok=True)
    checked.write_text(emit_checked(source, specs, src_name=f"{name}.py"))
    proc = subprocess.run(
        [exe, "check", str(checked), "--analysis_kind", "icontract",
         "--per_condition_timeout", str(per_condition_timeout)],
        capture_output=True, text=True, timeout=per_condition_timeout * 40 + 120,
    )
    if proc.returncode == 0:
        return "clean", ""
    if proc.returncode == 1:
        return "counterexample", (proc.stdout + proc.stderr).strip().splitlines()[0] if (proc.stdout + proc.stderr).strip() else ""
    return ERROR, f"crosshair exited {proc.returncode}"


def run_task(
    task_dir: Path,
    workdir: Path,
    mutant_cap: int = 8,
    hunt_timeout: int = 5,
    dafny_time_limit: int = 60,
    difftest_examples: int = 60,
) -> TaskScore:
    task_id = task_dir.name
    score = TaskScore(task_id=task_id)
    source_path = task_dir / "task.py"
    source = source_path.read_text()
    workdir.mkdir(parents=True, exist_ok=True)

    # R0: gate
    specs = parse_source(source, filename=str(source_path))
    if specs.errors or specs.orphans:
        score.rungs.append(Rung("gate", FAIL, "spec errors"))
        return score
    gate = run_type_gate([source_path])
    if not gate.available:
        score.rungs.append(Rung("gate", ERROR, gate.error or "type gate unavailable"))
    elif gate.errors:
        score.rungs.append(Rung("gate", FAIL, f"{len(gate.errors)} type error(s)"))
        return score
    else:
        score.rungs.append(Rung("gate", PASS))

    # R1: hunt
    verdict, detail = _hunt(source, task_id, workdir / "hunt", hunt_timeout)
    if verdict == "clean":
        score.rungs.append(Rung("hunt", PASS))
    else:
        score.rungs.append(Rung("hunt", FAIL if verdict == "counterexample" else ERROR, detail))
        return score

    # R2: mutant panel (spec strength)
    meta_path = task_dir / "meta.json"
    equivalents: set[str] = set()
    if meta_path.exists():
        meta = json.loads(meta_path.read_text())
        # Adjudicated equivalent mutants: same output on every input, so no
        # spec can kill them — excluded from the panel, counted visibly.
        equivalents = set(meta.get("equivalent_mutants", []))
    mutants = generate_mutations(source, max_mutants=mutant_cap)
    score.adjudicated = sum(1 for d, _ in mutants if d in equivalents)
    mutants = [(d, m) for d, m in mutants if d not in equivalents]
    score.mutants_total = len(mutants)
    for i, (description, mutated) in enumerate(mutants):
        verdict, _ = _hunt(mutated, f"{task_id}_m{i}", workdir / "mutants", hunt_timeout)
        if verdict == "counterexample":
            score.mutants_killed += 1
        elif verdict == "clean":
            score.survivors.append(description)
        # errors excluded from both counts
    if score.mutants_total == 0:
        score.rungs.append(Rung("mutants", SKIP, "no mutation sites"))
    elif score.survivors:
        score.rungs.append(Rung(
            "mutants", FAIL,
            f"{score.mutants_killed}/{score.mutants_total} killed; "
            f"survivors: {'; '.join(score.survivors[:3])}",
        ))
    else:
        score.rungs.append(Rung("mutants", PASS, f"{score.mutants_killed}/{score.mutants_total} killed"))

    # R3: encode
    try:
        sidecar = load_proof_sidecar(source_path)
        encoded = encode_module(source, specs, module_name=source_path.name,
                                proof_lemmas=sidecar.lemmas)
    except EncodeError as exc:
        score.rungs.append(Rung("encode", FAIL, f"line {exc.line}: {exc.message}"))
        return score
    score.rungs.append(Rung("encode", PASS))

    # R4: prove
    if find_dafny() is None:
        score.rungs.append(Rung("prove", ERROR, "dafny not installed"))
        return score
    stub = workdir / f"{task_id}.dfy"
    stub.write_text(encoded.dafny_source + sidecar.text)
    result = verify_dafny_file(stub, encoded.line_map, time_limit=dafny_time_limit)
    if result.error is not None:
        score.rungs.append(Rung("prove", ERROR, result.error))
        return score
    if not result.ok:
        first = next((d for d in result.diagnostics if d.severity == "error"), None)
        score.rungs.append(Rung("prove", FAIL, first.message if first else "verification failed"))
        return score
    score.rungs.append(Rung("prove", PASS))

    # R5: fidelity
    try:
        from ..difftest.harness import difftest_file
        diff = difftest_file(source_path, workdir / "difftest", examples=difftest_examples)
    except Exception as exc:  # hypothesis/runtime not installed etc.
        score.rungs.append(Rung("fidelity", ERROR, f"{type(exc).__name__}: {exc}"))
        return score
    if diff.error is not None:
        score.rungs.append(Rung("fidelity", ERROR, diff.error))
    elif all(f.ok for f in diff.functions):
        score.rungs.append(Rung("fidelity", PASS, f"{difftest_examples} examples/function"))
    else:
        bad = next(f for f in diff.functions if not f.ok)
        score.rungs.append(Rung("fidelity", FAIL, f"{bad.name}: {bad.mismatch or bad.error}"))
    return score


def run_gauntlet(tasks_root: Path, workdir: Path, **kwargs) -> list[TaskScore]:
    scores = []
    for task_dir in sorted(p for p in tasks_root.iterdir() if (p / "task.py").exists()):
        scores.append(run_task(task_dir, workdir / task_dir.name, **kwargs))
    return scores


def render_report(scores: list[TaskScore]) -> str:
    names = ["gate", "hunt", "mutants", "encode", "prove", "fidelity"]
    lines = []
    header = f"{'task':<22} " + " ".join(f"{n:<8}" for n in names) + " height"
    lines.append(header)
    lines.append("-" * len(header))
    mark = {PASS: "pass", FAIL: "FAIL", ERROR: "err", SKIP: "skip"}
    for s in scores:
        by_name = {r.name: r for r in s.rungs}
        cells = []
        for n in names:
            r = by_name.get(n)
            if r is None:
                cells.append(f"{'-':<8}")
            elif n == "mutants" and s.mutants_total:
                cells.append(f"{f'{s.mutants_killed}/{s.mutants_total}':<8}")
            else:
                cells.append(f"{mark[r.status]:<8}")
        lines.append(f"{s.task_id:<22} " + " ".join(cells) + f" {s.height}/6")
    full = sum(1 for s in scores if s.height == 6)
    killed = sum(s.mutants_killed for s in scores)
    total = sum(s.mutants_total for s in scores)
    lines.append("-" * len(header))
    lines.append(
        f"tasks: {len(scores)}   full-ladder: {full}   "
        f"spec strength: {killed}/{total} mutants killed"
        + (f" ({100 * killed / total:.0f}%)" if total else "")
    )
    return "\n".join(lines)


def scores_to_json(scores: list[TaskScore]) -> dict:
    return {
        "tasks": [
            {
                "id": s.task_id,
                "height": s.height,
                "rungs": [{"name": r.name, "status": r.status, "detail": r.detail} for r in s.rungs],
                "mutants": {"total": s.mutants_total, "killed": s.mutants_killed,
                            "survivors": s.survivors, "adjudicated_equivalent": s.adjudicated},
            }
            for s in scores
        ],
    }
