"""Experiment harness: exams as a matrix of (task x engine x arm x trial).

The paper-grade wrapper around the single-run exam primitives. Three arms
isolate what the toolchain contributes:

- ``full``     the repair loop with structured-failure feedback (the product)
- ``one-shot`` a single proposal, then judgment — no loop
- ``ablated``  the loop runs, but the engine sees only "verification
               failed" — measures the value of structured diagnostics

Every (task, engine, arm, trial) cell appends one JSONL row to an
append-only ledger, flushed immediately: an interrupted overnight matrix
resumes without re-running completed cells, and every reported number is
regenerable from the ledger alone.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import shutil
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ..repair import Engine, make_engine
from .exam import ExamScore, exam_tasks, run_repair_exam
from .specexam import SpecExamScore, run_spec_exam, spec_exam_tasks

ARMS = ("full", "one-shot", "ablated")
EXAMS = ("proof-repair", "spec-writing")
# The spec-writing exam has no loop to ablate and no budget to vary: its
# arms would all be the same run.
SPEC_ARMS = ("one-shot",)
# NOT bumped when `comparable` and the timeout identities were added to
# spec-writing rows. `_rows` drops every row whose schema does not match, so
# a bump discards the whole ledger — including proof-repair rows, which this
# has nothing to do with. A ledger is an append-only RECORD that cannot be
# recomputed (unlike the golden cache, which is versioned for exactly this
# reason). A row missing the field is handled where it matters instead: its
# comparability is UNKNOWN, which `_quotable` refuses to read as comparable.
TRIAL_SCHEMA = "lemmapy-exam-trial/1"
RUN_SCHEMA = "lemmapy-exam-run/1"


def redact_failures(request: dict[str, Any]) -> dict[str, Any]:
    """Arm C: same loop, generic feedback. Keeps rules/source/current
    sidecar/attempt (loop STATE — the engine's own prior output); replaces
    the structured verification payload and per-attempt failure detail
    with 'verification failed'."""
    redacted = dict(request)
    failures = request.get("failures") or {}
    redacted["failures"] = {
        "schema": failures.get("schema"),
        "status": failures.get("status"),
        "message": "verification failed",
    }
    redacted["history"] = [
        {"attempt": h.get("attempt"), "proposal": h.get("proposal"),
         "failures": "verification failed"}
        for h in request.get("history", [])
    ]
    return redacted


class _AblatedEngine:
    """Wraps any engine so it sees redacted requests. Usage passes
    through, so ledger accounting is arm-independent."""

    def __init__(self, inner: Engine):
        self.inner = inner

    def __call__(self, request: dict[str, Any]) -> str:
        return self.inner(redact_failures(request))

    @property
    def usage_log(self) -> list[dict[str, Any] | None]:
        return getattr(self.inner, "usage_log", [])


def _arm_config(spec: str, arm: str, max_iterations: int,
                effort: str | None = None):
    """(engine_factory, max_iterations) for one arm of one engine."""
    if arm == "full":
        return (lambda: make_engine(spec, effort=effort)), max_iterations
    if arm == "one-shot":
        return (lambda: make_engine(spec, effort=effort)), 1
    if arm == "ablated":
        return (lambda: _AblatedEngine(make_engine(spec, effort=effort))), \
            max_iterations
    raise ValueError(f"unknown arm {arm!r} (use one of {', '.join(ARMS)})")


def _slug(spec: str) -> str:
    """Filesystem-safe cell-directory name for an engine spec."""
    if spec.startswith("file:"):
        return "file-" + hashlib.sha256(spec.encode()).hexdigest()[:8]
    return re.sub(r"[^A-Za-z0-9._-]+", "-", spec)


def _display(spec: str, width: int = 24) -> str:
    """Table-safe engine label. A `file:<dir>` replay spec carries a long
    absolute path that would wreck the columns; keep the tail, which is the
    part that identifies the replay set. Ledger rows keep the full spec."""
    if len(spec) <= width:
        return spec
    return "…" + spec[-(width - 1):]


def _git_rev(cwd: Path) -> str | None:
    try:
        proc = subprocess.run(["git", "rev-parse", "HEAD"], cwd=cwd,
                              capture_output=True, text=True, timeout=10)
    except OSError:
        return None
    return proc.stdout.strip() if proc.returncode == 0 else None


def _claude_version() -> str | None:
    exe = shutil.which("claude")
    if exe is None:
        return None
    try:
        proc = subprocess.run([exe, "--version"], capture_output=True,
                              text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return proc.stdout.strip() if proc.returncode == 0 else None


def _now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def completed_cells(ledger: Path) -> set[tuple[str, str, str, str, int]]:
    """(exam, task, engine, arm, trial) tuples already recorded. Tolerant
    of a torn tail line (a crash mid-append must not poison resume)."""
    done: set[tuple[str, str, str, str, int]] = set()
    if not ledger.exists():
        return done
    for line in ledger.read_text().splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if row.get("schema") != TRIAL_SCHEMA:
            continue
        done.add((row["exam"], row["task"], row["engine"], row["arm"],
                  row["trial"]))
    return done


def _usage_total(usage: list[dict[str, Any] | None]) -> dict[str, Any]:
    total: dict[str, Any] = {"input_tokens": None, "output_tokens": None,
                             "cost_usd": None}
    for key in ("input_tokens", "output_tokens", "cost_usd"):
        vals = [u[key] for u in usage if u and u.get(key) is not None]
        if vals:
            total[key] = round(sum(vals), 6) if key == "cost_usd" else sum(vals)
    return total


def _score_row(score: ExamScore, *, run_id: str, exam: str, engine: str,
               arm: str, trial: int, max_iterations: int,
               time_limit: int) -> dict[str, Any]:
    proposals = sum(1 for a in score.attempts if a.get("engine_ms") is not None)
    rejections = sum(1 for a in score.attempts if a.get("rejection"))
    return {
        "schema": TRIAL_SCHEMA, "run_id": run_id, "exam": exam,
        "task": score.task_id, "engine": engine, "arm": arm, "trial": trial,
        "restored": score.restored, "iterations": score.iterations,
        "reason": score.reason, "attempts": score.attempts,
        "proposals": proposals, "rejections": rejections,
        "golden_lemmas": len(score.golden_lemmas),
        "usage": score.usage, "usage_total": _usage_total(score.usage),
        "wall_ms": score.wall_ms, "max_iterations": max_iterations,
        "time_limit": time_limit, "ts": _now(),
    }


def _spec_row(score: SpecExamScore, *, run_id: str, engine: str, arm: str,
              trial: int, time_limit: int) -> dict[str, Any]:
    """A spec-writing row. `restored` carries EXAM VALIDITY so the summary's
    k/n column stays meaningful across exams; spec strength lives in the
    mutants fields, which is what the paper reports."""
    return {
        "schema": TRIAL_SCHEMA, "run_id": run_id, "exam": "spec-writing",
        "task": score.task_id, "engine": engine, "arm": arm, "trial": trial,
        "restored": score.valid, "iterations": score.attempts,
        "reason": score.reason, "attempts": [],
        "proposals": score.attempts, "rejections": len(score.retry_reasons),
        "golden_lemmas": 0,
        "height": score.height, "golden_height": score.golden_height,
        # `mutants_total` is the SCORED denominator (golden's panel), so an
        # invalid or refuted answer counts 0/N rather than vanishing.
        "mutants_total": score.scored_total,
        "engine_panel_total": score.mutants_total,
        "mutants_killed": score.mutants_killed,
        "mutants_crashed": score.mutants_crashed,
        "golden_mutants_total": score.golden_mutants_total,
        "golden_mutants_killed": score.golden_mutants_killed,
        # The timeout-bias verdict, carried INTO the ledger. Without it the
        # ledger's own spec-strength line re-pooled rows the exam report had
        # just marked unquotable — the same defect one level up, where the
        # `!` marking no longer travels with the row.
        "comparable": score.comparable,
        "timeout_mutants": sorted(score.timeout_mutants),
        "golden_timeout_mutants": sorted(score.golden_timeout_mutants),
        "survivors": score.survivors, "clause_counts": score.clause_counts,
        "retry_reasons": score.retry_reasons,
        "rules_version": score.rules_version,
        "usage": score.usage, "usage_total": _usage_total(score.usage),
        "wall_ms": score.wall_ms, "max_iterations": 1,
        "time_limit": time_limit, "ts": _now(),
    }


def _append(ledger: Path, row: dict[str, Any]) -> None:
    with open(ledger, "a") as fh:
        fh.write(json.dumps(row) + "\n")
        fh.flush()


def run_experiment(tasks_root: Path, workdir: Path, engines: list[str],
                   arms: list[str], trials: int, ledger: Path,
                   max_iterations: int = 4, time_limit: int = 60,
                   only_tasks: set[str] | None = None,
                   resume: bool = True, exam: str = "proof-repair",
                   retries: int = 2, ladder: dict[str, Any] | None = None,
                   engine_effort: str | None = None,
                   progress=None) -> list[dict[str, Any]]:
    """Run an exam over the full matrix, appending one row per
    (task, engine, arm, trial) to the ledger. Returns the rows written by
    THIS invocation (resumed cells are skipped, not re-emitted)."""
    # Fail fast on config errors before any engine spends tokens.
    if exam not in EXAMS:
        raise ValueError(f"unknown exam {exam!r} (use one of {', '.join(EXAMS)})")
    for spec in engines:
        make_engine(spec, effort=engine_effort)
    allowed = ARMS if exam == "proof-repair" else SPEC_ARMS
    for arm in arms:
        if arm not in allowed:
            raise ValueError(
                f"unknown arm {arm!r} for exam {exam!r} "
                f"(use one of {', '.join(allowed)})")
    roster = exam_roster(tasks_root, exam)
    roster_desc = ("sidecar-bearing roster" if exam == "proof-repair"
                   else "roster")
    if only_tasks is not None:
        unknown = only_tasks - set(roster)
        if unknown:
            raise ValueError(
                f"unknown task(s) {sorted(unknown)}; {roster_desc}: {roster}")
        roster = [t for t in roster if t in only_tasks]
    if not roster:
        raise ValueError(f"no {exam} exam tasks under {tasks_root}")

    ledger.parent.mkdir(parents=True, exist_ok=True)
    run_id = f"run-{_now()}-{hashlib.sha256(repr((engines, arms, trials)).encode()).hexdigest()[:6]}"
    ladder_kwargs = dict(ladder or {})
    _append(ledger, {
        "schema": RUN_SCHEMA, "run_id": run_id, "ts": _now(), "exam": exam,
        "git_rev": _git_rev(tasks_root), "claude_version": _claude_version(),
        # An unrecorded effort is a hidden variable in every cross-model
        # comparison; "cli-default" is itself a recorded condition.
        "engine_effort": engine_effort or "cli-default",
        "engines": engines, "arms": arms, "trials": trials,
        "max_iterations": max_iterations, "time_limit": time_limit,
        "retries": retries, "ladder": ladder_kwargs,
        "tasks_root": str(tasks_root), "roster": roster,
    })

    done = completed_cells(ledger) if resume else set()
    written: list[dict[str, Any]] = []
    for spec in engines:
        for arm in arms:
            factory, arm_iters = _arm_config(spec, arm, max_iterations,
                                             effort=engine_effort)
            for trial in range(trials):
                pending = {t for t in roster
                           if (exam, t, spec, arm, trial) not in done}
                if not pending:
                    continue
                if progress is not None:
                    progress(f"[{exam} / {spec} / {arm} / trial {trial}] "
                             f"{len(pending)} task(s)")
                cell_dir = workdir / _slug(spec) / arm / f"trial{trial}"
                if exam == "proof-repair":
                    rows = [
                        _score_row(score, run_id=run_id, exam=exam,
                                   engine=spec, arm=arm, trial=trial,
                                   max_iterations=arm_iters,
                                   time_limit=time_limit)
                        for score in run_repair_exam(
                            tasks_root, cell_dir, factory,
                            max_iterations=arm_iters, time_limit=time_limit,
                            only=pending)
                    ]
                else:
                    rows = [
                        _spec_row(score, run_id=run_id, engine=spec, arm=arm,
                                  trial=trial, time_limit=time_limit)
                        for score in run_spec_exam(
                            tasks_root, cell_dir, factory, retries=retries,
                            only=pending, **ladder_kwargs)
                    ]
                for row in rows:
                    _append(ledger, row)
                    written.append(row)
    return written


def _rows(ledger: Path) -> list[dict[str, Any]]:
    """Trial rows, LAST row winning per cell (a --no-resume rerun appends;
    the newest measurement is the one reported)."""
    latest: dict[tuple, dict[str, Any]] = {}
    for line in ledger.read_text().splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if row.get("schema") != TRIAL_SCHEMA:
            continue
        latest[(row["exam"], row["task"], row["engine"], row["arm"],
                row["trial"])] = row
    return list(latest.values())


def exam_roster(tasks_root: Path, exam: str) -> list[str]:
    """Task ids an exam runs over today. The single source of truth for
    both the matrix driver and the status query — a ledger outlives the
    corpus, so 'which tasks count' must be answered from the corpus, never
    from what happens to be recorded."""
    if exam == "proof-repair":
        return [d.name for d in exam_tasks(tasks_root)]
    return [d.name for d in spec_exam_tasks(tasks_root)]


def matrix_rows(ledger: Path, *, exam: str, engines: list[str],
                arms: list[str], trials: int,
                tasks: set[str] | None = None) -> list[dict[str, Any]]:
    """Latest ledger row for every cell of the REQUESTED matrix.

    Exit status must reflect the whole matrix, not just the cells this
    invocation happened to run. `run_experiment` returns only newly written
    rows so that resume stays idempotent — which means a resumed run whose
    failures were all recorded earlier would otherwise look like a clean
    pass to CI.

    `tasks` scopes the query to the roster the run actually covered. Pass
    it whenever the ledger may outlive a corpus change: a ledger is
    append-only, so a task later renamed or dropped keeps its historical
    rows forever, and an unsuccessful one would fail a matrix that no
    longer contains that task. `None` means "every task in the ledger" and
    is only safe for a ledger known to match the current corpus.
    """
    if not ledger.exists():
        return []
    want_engines, want_arms = set(engines), set(arms)
    return [
        row for row in _rows(ledger)
        if row["exam"] == exam
        and row["engine"] in want_engines
        and row["arm"] in want_arms
        and row["trial"] < trials
        and (tasks is None or row["task"] in tasks)
    ]


def summarize_ledger(ledger: Path) -> str:
    """The headline table: per (task, engine, arm) — restored k/n, mean
    iterations among restorations, whitelist-rejection rate, tokens."""
    rows = _rows(ledger)
    if not rows:
        return f"no trial rows in {ledger}"
    groups: dict[tuple[str, str, str, str], list[dict[str, Any]]] = {}
    for row in rows:
        groups.setdefault(
            (row["exam"], row["task"], row["engine"], row["arm"]), []
        ).append(row)
    header = (f"{'exam':<13} {'task':<16} {'engine':<26} {'arm':<9} "
              f"{'ok':<7} {'iters':<6} {'rej%':<6} {'kill%':<7} "
              f"{'golden%':<8} {'out-tok':<8}")
    lines = [header, "-" * len(header)]
    rules: dict[str, int] = {}
    for key in sorted(groups):
        cell = groups[key]
        exam, task, engine, arm = key
        n = len(cell)
        k = sum(1 for r in cell if r["restored"])
        iters = [r["iterations"] for r in cell if r["restored"]]
        mean_iters = f"{sum(iters) / len(iters):.1f}" if iters else "-"
        proposals = sum(r["proposals"] for r in cell)
        rejections = sum(r["rejections"] for r in cell)
        rej = f"{100 * rejections / proposals:.0f}" if proposals else "-"
        out_tok = sum(r["usage_total"]["output_tokens"] or 0 for r in cell)
        quotable = _quotable(cell)
        kill = _rate(quotable, "mutants_killed", "mutants_total")
        golden = _rate(quotable, "golden_mutants_killed", "golden_mutants_total")
        if len(quotable) < len(cell):
            kill += "!"  # some trials failed the timeout-bias check
        lines.append(f"{exam:<13} {task:<16} {_display(engine):<26} {arm:<9} "
                     f"{f'{k}/{n}':<7} {mean_iters:<6} {rej:<6} {kill:<7} "
                     f"{golden:<8} {out_tok or '-':<8}")
        for row in cell:
            for a in row["attempts"]:
                if a.get("rejection"):
                    rule = a["rejection"].get("rule") or "other"
                    rules[rule] = rules.get(rule, 0) + 1
    lines.append("-" * len(header))
    # Per (engine, arm) aggregate over all tasks and trials — the row a
    # results table is built from, with a Wilson 95% interval because k/n
    # at these trial counts is not a defensible point estimate on its own.
    cells: dict[tuple[str, str, str], list[dict[str, Any]]] = {}
    for row in rows:
        cells.setdefault((row["exam"], row["engine"], row["arm"]), []).append(row)
    lines.append(f"{'exam':<13} {'engine':<26} {'arm':<9} {'ok':<8} "
                 f"{'rate':<7} {'95% CI':<11} {'kill%':<7} {'cost$':<8}")
    for key in sorted(cells):
        exam, engine, arm = key
        cell = cells[key]
        n = len(cell)
        k = sum(1 for r in cell if r["restored"])
        cost = sum(r["usage_total"]["cost_usd"] or 0 for r in cell)
        lines.append(
            f"{exam:<13} {_display(engine):<26} {arm:<9} {f'{k}/{n}':<8} "
            f"{f'{100 * k / n:.0f}%':<7} {_ci(k, n):<11} "
            f"{_rate(_quotable(cell), 'mutants_killed', 'mutants_total'):<7} "
            f"{f'{cost:.2f}' if cost else '-':<8}")
    lines.append("-" * len(header))
    total = len(rows)
    restored = sum(1 for r in rows if r["restored"])
    lines.append(f"trials: {total}   ok (restored/valid): {restored}/{total} "
                 f"{_ci(restored, total)}")
    spec_rows = [r for r in rows if r["exam"] == "spec-writing"]
    if spec_rows:
        quotable = _quotable(spec_rows)
        dropped = len(spec_rows) - len(quotable)
        if not quotable:
            lines.append(
                f"spec strength: NOT AGGREGATED — none of the {len(spec_rows)} "
                f"spec-writing trial(s) passed the timeout-bias check (or all "
                f"predate it), so there is no comparable pair to pool")
        else:
            lines.append(
                f"spec strength: engine "
                f"{_rate(quotable, 'mutants_killed', 'mutants_total')}"
                f" vs golden "
                f"{_rate(quotable, 'golden_mutants_killed', 'golden_mutants_total')}"
                f"   (refutations only — crashes never credited; every "
                f"attempted task scored over GOLDEN's panel, so a failed "
                f"answer is 0/N, not excluded)"
                + (f"\n  — over the {len(quotable)}/{len(spec_rows)} trial(s) "
                   f"whose two arms went inconclusive on the SAME mutants; "
                   f"{dropped} excluded by the timeout-bias check or written "
                   f"before it existed, so this is not a whole-matrix rate"
                   if dropped else ""))
    if rules:
        breakdown = ", ".join(f"{r}: {c}" for r, c in sorted(rules.items()))
        lines.append(f"whitelist rejections by rule: {breakdown}")
    return "\n".join(lines)


def wilson_interval(successes: int, trials: int,
                    z: float = 1.96) -> tuple[float, float]:
    """Wilson score interval (95% by default) for a binomial proportion.

    The normal approximation is indefensible at these trial counts — with
    5/5 it reports [1.0, 1.0], claiming certainty from five observations.
    Wilson stays inside [0, 1] and keeps a sane width at the boundaries,
    which is what a reviewer will expect next to any small-n rate.
    """
    if trials <= 0:
        return (0.0, 1.0)
    p = successes / trials
    denom = 1 + z * z / trials
    center = (p + z * z / (2 * trials)) / denom
    margin = z * math.sqrt(p * (1 - p) / trials
                           + z * z / (4 * trials * trials)) / denom
    return (max(0.0, center - margin), min(1.0, center + margin))


def _ci(successes: int, trials: int) -> str:
    lo, hi = wilson_interval(successes, trials)
    return f"[{100 * lo:.0f},{100 * hi:.0f}]"


def _quotable(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Spec-writing rows whose refutation gap is a strength difference.

    A row whose two arms went inconclusive on DIFFERENT mutants mixes hunt
    cost into that gap, and the exam report already refuses to quote it. A
    row written before the check existed carries no verdict at all: absent
    is not the same as comparable, and defaulting it to True would restore
    the biased rate on exactly the historical data nobody can re-examine.
    Both are dropped, and the caller says how many.
    """
    return [r for r in rows
            if r["exam"] != "spec-writing" or r.get("comparable") is True]


def _rate(rows: list[dict[str, Any]], killed_key: str, total_key: str) -> str:
    """Pooled percentage over rows that HAVE a panel. Rows without one (a
    proof-repair row, or an invalid spec answer) are excluded rather than
    counted as zero — 'no panel run' is not 'killed nothing'."""
    total = sum(r.get(total_key) or 0 for r in rows)
    if not total:
        return "-"
    killed = sum(r.get(killed_key) or 0 for r in rows)
    return f"{100 * killed / total:.0f}%"


def ledger_to_json(ledger: Path) -> dict[str, Any]:
    """Machine-readable view for plotting: run headers + latest trial rows."""
    headers = []
    for line in ledger.read_text().splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if row.get("schema") == RUN_SCHEMA:
            headers.append(row)
    return {"runs": headers, "trials": _rows(ledger)}
