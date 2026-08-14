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
import re
import shutil
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ..repair import Engine, make_engine
from .exam import ExamScore, exam_tasks, run_repair_exam

ARMS = ("full", "one-shot", "ablated")
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


def _arm_config(spec: str, arm: str, max_iterations: int):
    """(engine_factory, max_iterations) for one arm of one engine."""
    if arm == "full":
        return (lambda: make_engine(spec)), max_iterations
    if arm == "one-shot":
        return (lambda: make_engine(spec)), 1
    if arm == "ablated":
        return (lambda: _AblatedEngine(make_engine(spec))), max_iterations
    raise ValueError(f"unknown arm {arm!r} (use one of {', '.join(ARMS)})")


def _slug(spec: str) -> str:
    """Filesystem-safe cell-directory name for an engine spec."""
    if spec.startswith("file:"):
        return "file-" + hashlib.sha256(spec.encode()).hexdigest()[:8]
    return re.sub(r"[^A-Za-z0-9._-]+", "-", spec)


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


def _append(ledger: Path, row: dict[str, Any]) -> None:
    with open(ledger, "a") as fh:
        fh.write(json.dumps(row) + "\n")
        fh.flush()


def run_experiment(tasks_root: Path, workdir: Path, engines: list[str],
                   arms: list[str], trials: int, ledger: Path,
                   max_iterations: int = 4, time_limit: int = 60,
                   only_tasks: set[str] | None = None,
                   resume: bool = True,
                   progress=None) -> list[dict[str, Any]]:
    """Run the proof-repair exam over the full matrix, appending one row
    per (task, engine, arm, trial) to the ledger. Returns the rows written
    by THIS invocation (resumed cells are skipped, not re-emitted)."""
    # Fail fast on config errors before any engine spends tokens.
    for spec in engines:
        make_engine(spec)
    for arm in arms:
        if arm not in ARMS:
            raise ValueError(f"unknown arm {arm!r} (use one of {', '.join(ARMS)})")
    roster = [d.name for d in exam_tasks(tasks_root)]
    if only_tasks is not None:
        unknown = only_tasks - set(roster)
        if unknown:
            raise ValueError(
                f"unknown task(s) {sorted(unknown)}; sidecar-bearing roster: "
                f"{roster}")
        roster = [t for t in roster if t in only_tasks]
    if not roster:
        raise ValueError(f"no sidecar-bearing exam tasks under {tasks_root}")

    ledger.parent.mkdir(parents=True, exist_ok=True)
    run_id = f"run-{_now()}-{hashlib.sha256(repr((engines, arms, trials)).encode()).hexdigest()[:6]}"
    _append(ledger, {
        "schema": RUN_SCHEMA, "run_id": run_id, "ts": _now(),
        "git_rev": _git_rev(tasks_root), "claude_version": _claude_version(),
        "engines": engines, "arms": arms, "trials": trials,
        "max_iterations": max_iterations, "time_limit": time_limit,
        "tasks_root": str(tasks_root), "roster": roster,
    })

    done = completed_cells(ledger) if resume else set()
    written: list[dict[str, Any]] = []
    for spec in engines:
        for arm in arms:
            factory, arm_iters = _arm_config(spec, arm, max_iterations)
            for trial in range(trials):
                pending = {t for t in roster
                           if ("proof-repair", t, spec, arm, trial) not in done}
                if not pending:
                    continue
                if progress is not None:
                    progress(f"[{spec} / {arm} / trial {trial}] "
                             f"{len(pending)} task(s)")
                cell_dir = workdir / _slug(spec) / arm / f"trial{trial}"
                scores = run_repair_exam(
                    tasks_root, cell_dir, factory,
                    max_iterations=arm_iters, time_limit=time_limit,
                    only=pending)
                for score in scores:
                    row = _score_row(
                        score, run_id=run_id, exam="proof-repair",
                        engine=spec, arm=arm, trial=trial,
                        max_iterations=arm_iters, time_limit=time_limit)
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
              f"{'restored':<9} {'iters':<6} {'rej%':<6} {'out-tok':<8}")
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
        lines.append(f"{exam:<13} {task:<16} {engine:<26} {arm:<9} "
                     f"{f'{k}/{n}':<9} {mean_iters:<6} {rej:<6} "
                     f"{out_tok or '-':<8}")
        for row in cell:
            for a in row["attempts"]:
                if a.get("rejection"):
                    rule = a["rejection"].get("rule") or "other"
                    rules[rule] = rules.get(rule, 0) + 1
    lines.append("-" * len(header))
    total = len(rows)
    restored = sum(1 for r in rows if r["restored"])
    lines.append(f"trials: {total}   restored: {restored}/{total}")
    if rules:
        breakdown = ", ".join(f"{r}: {c}" for r, c in sorted(rules.items()))
        lines.append(f"whitelist rejections by rule: {breakdown}")
    return "\n".join(lines)


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
