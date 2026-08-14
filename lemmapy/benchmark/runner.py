"""lemmapy-benchmark: the native benchmark runner.

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

from ..agentio import atomic_write_text
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
    mutants_killed: int = 0   # REFUTED by the specification
    mutants_crashed: int = 0  # caught by the interpreter, not by the spec
    survivors: list[str] = field(default_factory=list)
    crashers: list[str] = field(default_factory=list)
    adjudicated: int = 0  # mutants ruled equivalent in meta.json, excluded
    timeouts: list[str] = field(default_factory=list)  # inconclusive, unadjudicated
    # Wall exhaustions ruled divergent in meta.json. Named, not counted: a
    # cross-arm timeout comparison has to know WHICH mutants went
    # inconclusive, and a bare count cannot answer that.
    adjudicated_timeouts: list[str] = field(default_factory=list)

    @property
    def timeout_mutants(self) -> list[str]:
        """Mutants whose hunt exhausted its wall — inconclusive, whether or
        not a human later ruled the divergence. Comparing two arms' kill
        rates is only meaningful when the two arms went inconclusive on the
        SAME mutants: otherwise the gap mixes spec strength with hunt cost."""
        return sorted(self.timeouts + self.adjudicated_timeouts)

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


# A CrossHair diagnostic that begins "false when calling" is a CONTRACT
# refutation — the specification itself was violated. Anything else it
# reports (IndexError, ZeroDivisionError, TypeError, ...) is the
# interpreter catching a fault, which every specification "catches"
# equally, including `#@ ensures True`. Crediting those to the spec is what
# gave a tautology 38% spec strength on this corpus.
_REFUTATION_MARKER = "error: false when calling"


def _hunt(source: str, name: str, workdir: Path, per_condition_timeout: int,
          wall: int | None = None) -> tuple[str, str]:
    """Emit runtime contracts and let CrossHair hunt. Returns (verdict,
    detail) with verdict one of: 'clean', 'counterexample' (the SPEC was
    refuted), 'crash' (an uncaught exception — a real fault, but not one
    the specification discriminated), 'timeout' (the wall was exhausted —
    inconclusive), or 'error'."""
    exe = _find_crosshair()
    if exe is None:
        return ERROR, "crosshair not installed"
    specs = parse_source(source)
    if specs.errors or specs.orphans:
        return ERROR, "spec errors"
    checked = workdir / f"{name}_checked.py"
    try:
        checked.parent.mkdir(parents=True, exist_ok=True)
        atomic_write_text(checked,
                          emit_checked(source, specs, src_name=f"{name}.py"))
    except OSError as exc:
        # Unwritable workdir degrades to a per-item ERROR, same as a
        # stuck analysis — never abort the run mid-scorecard.
        return ERROR, f"could not stage checked module: {type(exc).__name__}"
    try:
        proc = subprocess.run(
            [exe, "check", str(checked), "--analysis_kind", "icontract",
             "--per_condition_timeout", str(per_condition_timeout)],
            capture_output=True, text=True,
            timeout=wall if wall is not None else per_condition_timeout * 40 + 120,
        )
    except subprocess.TimeoutExpired:
        # A hunt that exhausts its wall is its own verdict: for mutants a
        # diverging loop is the common cause, and divergence is a behavior
        # change (this toolchain proves termination at R4).
        return "timeout", "hunt wall exceeded (nonterminating mutant?)"
    except OSError as exc:
        # An unlaunchable analysis must degrade to a per-item ERROR,
        # never abort the whole benchmark run mid-scorecard.
        return ERROR, f"crosshair failed to run: {type(exc).__name__}"
    if proc.returncode == 0:
        return "clean", ""
    if proc.returncode == 1:
        output = (proc.stdout + proc.stderr).strip()
        first = output.splitlines()[0] if output else ""
        if _REFUTATION_MARKER in output:
            return "counterexample", first
        return "crash", first
    return ERROR, f"crosshair exited {proc.returncode}"


def run_task(
    task_dir: Path,
    workdir: Path,
    mutant_cap: int = 12,
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

    # R1: hunt. A crash is as much a failure here as a refutation — the
    # module must be clean against its own specs either way.
    verdict, detail = _hunt(source, task_id, workdir / "hunt", hunt_timeout)
    if verdict == "clean":
        score.rungs.append(Rung("hunt", PASS))
    else:
        score.rungs.append(Rung(
            "hunt", FAIL if verdict in ("counterexample", "crash") else ERROR,
            detail))
        return score

    # R2: mutant panel (spec strength)
    meta_path = task_dir / "meta.json"
    equivalents: set[str] = set()
    timeout_adjudicated: set[str] = set()
    if meta_path.exists():
        meta = json.loads(meta_path.read_text())
        # Adjudicated equivalent mutants: same output on every input, so no
        # spec can kill them — excluded from the panel, counted visibly.
        equivalents = set(meta.get("equivalent_mutants", []))
        timeout_adjudicated = set(meta.get("timeout_kills", []))
    mutants = generate_mutations(source, max_mutants=mutant_cap)
    # Every adjudication must name EXACTLY ONE mutant. A ruling that
    # matches nothing is stale (a source edit shifted the site) or a typo;
    # one that matches several would apply a single human judgement to
    # several mutants. Either way the panel's meaning is unknown, so the
    # rung errors instead of scoring.
    #
    # Validate against the COMPLETE panel, not the capped one: --quick
    # truncates the panel, and a ruling about a mutant the truncated run
    # never hunts is out of scope, not stale. Generation is deterministic
    # and side-effect-free, and the capped panel is a prefix of the full
    # one, so this is cheap and stable.
    full_panel = [d for d, _ in generate_mutations(source, max_mutants=10**6)]
    panel_descriptions = [d for d, _ in mutants]
    stale: list[str] = []
    for key, entries in (("equivalent_mutants", equivalents),
                         ("timeout_kills", timeout_adjudicated)):
        for entry in sorted(entries):
            hits = full_panel.count(entry)
            if hits != 1:
                stale.append(
                    f"{key} entry {entry!r} matches {hits} mutants (expected 1)")
    # A mutant ruled BOTH equivalent (unkillable, exclude from the
    # denominator) and a timeout kill (diverges, count as killed) carries
    # contradictory human judgements. Each entry validates fine on its
    # own, and the equivalence filter would silently win — so name the
    # contradiction instead of resolving it by evaluation order.
    for entry in sorted(equivalents & timeout_adjudicated):
        stale.append(
            f"{entry!r} is ruled BOTH equivalent_mutants and timeout_kills "
            f"— contradictory")
    if stale:
        score.mutants_total = len(mutants)
        score.rungs.append(Rung(
            "mutants", ERROR,
            "adjudication does not match the panel: " + "; ".join(stale[:3])))
        return score
    error_reasons: list[str] = []
    score.adjudicated = sum(1 for d in panel_descriptions if d in equivalents)
    mutants = [(d, m) for d, m in mutants if d not in equivalents]
    score.mutants_total = len(mutants)
    for i, (description, mutated) in enumerate(mutants):
        # Mutants get a tighter wall than the original: a diverging mutant
        # would otherwise stall the panel for the full default wall.
        verdict, why = _hunt(mutated, f"{task_id}_m{i}", workdir / "mutants",
                             hunt_timeout, wall=hunt_timeout * 12 + 60)
        if verdict == "counterexample":
            score.mutants_killed += 1
        elif verdict == "crash":
            # The interpreter caught this fault, not the specification. A
            # tautological spec "kills" it just as well, so it carries no
            # information about spec strength and is never credited.
            score.mutants_crashed += 1
            score.crashers.append(description)
        elif verdict == "timeout":
            # A wall exhaustion is INCONCLUSIVE on its own: R4 proves the
            # original terminates, not the mutant, and a slow-but-
            # terminating analysis would be indistinguishable. A human
            # adjudicates divergence in meta.json ("timeout_kills"); until
            # then the timeout fails the rung, like a survivor.
            #
            # An adjudicated divergence is a real behaviour change and does
            # not fail the rung — but it is NOT credited as spec strength,
            # for exactly the reason crashes are not: the wall catches a
            # diverging mutant whatever the specification says, so
            # `#@ ensures True` "kills" it just as well and the mutant
            # carries no information about the spec.
            if description in timeout_adjudicated:
                score.adjudicated_timeouts.append(description)
            else:
                score.timeouts.append(description)
        elif verdict == "clean":
            score.survivors.append(description)
        else:
            # An errored analysis is excluded from all counts, so the
            # REASON is the only way to act on it — an intermittent
            # analysis failure is otherwise an unactionable "1 analysis
            # error(s)" with no way to tell a crashed hunter from a
            # misconfigured one.
            error_reasons.append(f"{description} ({why})")
    analysis_errors = (score.mutants_total - score.mutants_killed
                       - score.mutants_crashed
                       - len(score.adjudicated_timeouts)
                       - len(score.survivors) - len(score.timeouts))
    if score.mutants_total == 0 and score.adjudicated:
        # The panel existed but adjudication emptied it: nothing was
        # measured, so this must not read as a skipped-because-absent rung
        # (SKIP counts toward ladder height).
        score.rungs.append(Rung(
            "mutants", FAIL,
            f"panel emptied by adjudication: all {score.adjudicated} mutant(s) "
            f"ruled equivalent — spec strength unmeasured"))
    elif score.mutants_total == 0:
        score.rungs.append(Rung("mutants", SKIP, "no mutation sites"))
    elif analysis_errors:
        # An incomplete panel outranks an ordinary failure: errored mutants
        # are untested, and hiding them behind a survivor report would
        # misstate what was actually measured. The census names every
        # bucket so the printed numbers add up to the panel.
        detail = (f"{score.mutants_killed}/{score.mutants_total} refuted; "
                  f"{score.mutants_crashed} crashed; "
                  f"{len(score.survivors)} survivor(s); "
                  f"{len(score.adjudicated_timeouts)} diverged; "
                  f"{len(score.timeouts)} unadjudicated timeout(s); "
                  f"{analysis_errors} analysis error(s)")
        if score.survivors:
            detail += f"; survivors: {'; '.join(score.survivors[:3])}"
        if score.timeouts:
            detail += (f"; timeouts: {'; '.join(score.timeouts[:3])} "
                       f"-- adjudicate divergence via meta.json \"timeout_kills\"")
        if error_reasons:
            detail += f"; errors: {'; '.join(error_reasons[:3])}"
        score.rungs.append(Rung("mutants", ERROR, detail))
    elif score.survivors or score.timeouts:
        parts = [f"{score.mutants_killed}/{score.mutants_total} refuted"]
        if score.mutants_crashed:
            parts.append(f"{score.mutants_crashed} crashed")
        if score.adjudicated_timeouts:
            parts.append(f"{len(score.adjudicated_timeouts)} diverged")
        if score.survivors:
            parts.append(f"survivors: {'; '.join(score.survivors[:3])}")
        if score.timeouts:
            parts.append(
                f"unadjudicated timeout(s): {'; '.join(score.timeouts[:3])} "
                f"-- adjudicate divergence via meta.json \"timeout_kills\"")
        score.rungs.append(Rung("mutants", FAIL, "; ".join(parts)))
    else:
        extra = []
        if score.mutants_crashed:
            extra.append(f"{score.mutants_crashed} crashed")
        if score.adjudicated_timeouts:
            # Named "diverged", not "killed": adjudication established a
            # behaviour change, not that the SPEC discriminated it.
            extra.append(f"{len(score.adjudicated_timeouts)} diverged "
                         f"(adjudicated, not credited)")
        score.rungs.append(Rung(
            "mutants", PASS,
            f"{score.mutants_killed}/{score.mutants_total} refuted"
            + ("; " + "; ".join(extra) if extra else "")))

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
    result = verify_dafny_file(stub, encoded.line_map,
                               time_limit=dafny_time_limit,
                               stub_extent=encoded.dafny_source.count("\n") + 1)
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


def run_benchmark(tasks_root: Path, workdir: Path, **kwargs) -> list[TaskScore]:
    scores = []
    for task_dir in sorted(p for p in tasks_root.iterdir() if (p / "task.py").exists()):
        try:
            scores.append(run_task(task_dir, workdir / task_dir.name, **kwargs))
        except OSError as exc:
            # A task whose staging fails (unreadable source, unwritable
            # workdir) still gets a scorecard row instead of killing the run.
            score = TaskScore(task_id=task_dir.name)
            score.rungs.append(
                Rung("gate", ERROR, f"task staging failed: {type(exc).__name__}")
            )
            scores.append(score)
    return scores


# Below this, a per-task refutation RATE carries too little information to
# compare against another task's: 1/1 is one bit. Such panels still count
# in the corpus total (where they pool), but the per-task cell is marked so
# nobody reads "100%" off a single mutant.
LOW_RESOLUTION_PANEL = 3


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
            elif n == "mutants" and s.mutants_total and r.status != ERROR:
                # Ratio only for completed panels; an errored panel's kill
                # count is a lower bound, not a mutation score. A panel
                # containing human-asserted kills is starred so the table
                # never passes adjudication off as measurement, and a panel
                # too small for its rate to be comparable is marked "?" so
                # nobody reads 1/1 as though it meant what 8/8 does.
                star = "*" if s.adjudicated_timeouts or s.adjudicated else ""
                thin = "?" if s.mutants_total < LOW_RESOLUTION_PANEL else ""
                ratio = f"{s.mutants_killed}/{s.mutants_total}{star}{thin}"
                cells.append(f"{ratio:<8}")
            else:
                cells.append(f"{mark[r.status]:<8}")
        lines.append(f"{s.task_id:<22} " + " ".join(cells) + f" {s.height}/6")
    full = sum(1 for s in scores if s.height == 6)
    killed = sum(s.mutants_killed for s in scores)
    crashed = sum(s.mutants_crashed for s in scores)
    total = sum(s.mutants_total for s in scores)
    asserted = sum(len(s.adjudicated_timeouts) for s in scores)
    excluded = sum(s.adjudicated for s in scores)
    lines.append("-" * len(header))
    lines.append(
        f"tasks: {len(scores)}   full-ladder: {full}   "
        f"spec strength: {killed}/{total} mutants REFUTED by the specs"
        + (f" ({100 * killed / total:.0f}%)" if total else "")
        + (f"; {crashed} crashed (caught by the interpreter, not the spec — "
           f"never credited)" if crashed else "")
        + (f"; {asserted} diverged (adjudicated nontermination — caught by "
           f"the wall, not the spec, so never credited)" if asserted else "")
    )
    panels = sorted(s.mutants_total for s in scores if s.mutants_total)
    if panels:
        import statistics

        thin = sum(1 for n in panels if n < LOW_RESOLUTION_PANEL)
        lines.append(
            f"panel resolution: median {statistics.median(panels):g} "
            f"mutants/task, min {min(panels)}, max {max(panels)}"
            + (f"; {thin} task(s) marked ? — panel too small for a per-task "
               f"rate to be comparable" if thin else ""))
    if asserted or excluded:
        # The headline must not launder human judgement as measurement: say
        # exactly how much of it the panel rests on.
        notes = []
        if asserted:
            notes.append(f"{asserted} mutant(s) human-adjudicated as "
                         f"divergent; counted separately, NOT as spec strength")
        if excluded:
            notes.append(f"{excluded} mutant(s) excluded as adjudicated equivalent")
        lines.append("* " + "; ".join(notes))
    return "\n".join(lines)


def scores_to_json(scores: list[TaskScore]) -> dict:
    return {
        "tasks": [
            {
                "id": s.task_id,
                "height": s.height,
                "rungs": [{"name": r.name, "status": r.status, "detail": r.detail} for r in s.rungs],
                "mutants": {"total": s.mutants_total, "killed": s.mutants_killed,
                            "crashed": s.mutants_crashed, "crashers": s.crashers,
                            "diverged": len(s.adjudicated_timeouts),
                            "timeouts": s.timeouts,
                            "adjudicated_timeouts": s.adjudicated_timeouts,
                            "survivors": s.survivors, "adjudicated_equivalent": s.adjudicated},
            }
            for s in scores
        ],
    }
