"""Spec-writing exams: strip the specification, ask an engine to write it,
and measure how STRONG the result is.

The proof-repair exam asks "can the engine finish the proof?"; this one asks
the harder question — "can it say what the code should do, precisely enough
to be worth proving?" A specification that parses, type-checks, and verifies
can still be worthless (`#@ ensures True` climbs the whole ladder). The
mutant panel is what makes that mechanical: the SAME deterministic panel
scores golden and engine specs, and the kill rate says how many real faults
each spec can see.

Exam mechanics:

- The engine receives the bare implementation (every `#@` line removed) and
  returns the fully annotated source. Executable `assert` proof-hints are
  CODE and stay — the engine cannot add or remove them.
- A SOURCE-FREEZE validator enforces the one rule that makes the score mean
  anything: dropping full-line `#@` comments from the engine's answer must
  reproduce the stripped input EXACTLY. An engine that may edit the
  implementation can always weaken the task to fit a trivial spec.
- Retries fire only for MECHANICAL invalidity (unparseable Python, a freeze
  violation, `#@` parse errors, no postcondition at all). No verification
  outcome is ever fed back: iterating on prover feedback is the proof-repair
  exam, and conflating them would measure neither.
- `#@ proof` clauses are forbidden: this exam has no sidecar channel, so a
  proof clause could only name a lemma that does not exist.

Comparability is the whole game, so the golden baseline is scored under
IDENTICAL conditions (its own `#@ proof` clauses stripped, no sidecar
staged) — otherwise the engine would be compared against a golden run that
had lemmas available to it.
"""

from __future__ import annotations

import ast
import hashlib
import io
import json
import re
import time
import tokenize
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from ..frontend.extract import parse_source
from ..repair import Engine, _strip_fences
from .exam import prepare_exam_workspace
from .runner import TaskScore, run_task

SPEC_RULES = """\
You are writing `#@` specification comments for a verified-Python toolchain.
Reply with the COMPLETE annotated Python file and nothing else (no fences, no
commentary).

THE ONE HARD RULE: you may only INSERT full-line `#@` comments. Every
executable line — including blank lines, asserts, and docstrings — must come
back byte-for-byte unchanged. Any edit to the implementation is rejected.

Clause syntax (grammar v0):
- Contract block, directly above the `def` (no blank line between):
    #@ requires <bool expr>
    #@ ensures <bool expr>            -- may use `result` and `old(param)`
- Inside a loop body, as the first lines of the body:
    #@ invariant <bool expr>
    #@ decreases <int expr>
- Expressions: Python operators, plus `==>` (implies), `<==>` (iff), and
    forall X in range(A, B) :: BODY        exists X in range(A, B) :: BODY
    forall X in <list expr> :: BODY        exists X in <list expr> :: BODY
- Available: len, range, sum, min, max, abs, all, any, slicing `xs[a:b]`,
  indexing, arithmetic (`//`, `%`; no `/`, no `**`).
- Do NOT write `#@ proof` clauses — there is no lemma sidecar in this exam.

Write the STRONGEST specification you can that is TRUE of this implementation:
a postcondition that pins down the result exactly, not merely a property it
happens to satisfy. A specification weak enough to hold of a buggy version of
this function scores poorly."""

STRIP_ALL = "all"
STRIP_PROOF = "proof"

_SPEC_RE = re.compile(r"#@")
_EQUIV_LINE_RE = re.compile(r"^line (\d+): ")


class SpecExamError(Exception):
    """A task cannot be examined at all (corpus defect, not an engine failure)."""


@dataclass(frozen=True)
class FreezeViolation:
    line: int
    message: str


def _spec_comment_lines(source: str) -> dict[int, int]:
    """Line number -> column, for lines that are ONLY a `#@` comment.

    Tokenize-driven so `#@` inside a string literal or docstring is not a
    spec comment (matching `frontend.extract._spec_comments`). A `#@`
    comment trailing executable code is refused: the exam's whole
    correctness argument is that removing spec lines is invertible, and a
    trailing comment makes it not.
    """
    lines = source.split("\n")
    found: dict[int, int] = {}
    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(source).readline))
    except (tokenize.TokenError, IndentationError, SyntaxError) as exc:
        raise SpecExamError(f"cannot tokenize source: {exc}") from exc
    for tok in tokens:
        if tok.type != tokenize.COMMENT or not tok.string.startswith("#@"):
            continue
        row, col = tok.start
        if lines[row - 1][:col].strip():
            raise SpecExamError(
                f"line {row}: `#@` comment trailing executable code — the "
                f"exam requires full-line spec comments (stripping must be "
                f"invertible)")
        found[row] = col
    return found


def _clause_kind(line: str) -> str:
    """The clause keyword of a full-line `#@` comment ('' if absent)."""
    body = line.split("#@", 1)[1].strip()
    return body.split(None, 1)[0] if body else ""


def strip_specs(source: str, mode: str = STRIP_ALL) -> str:
    """Remove `#@` lines. `mode=STRIP_ALL` strips every clause (the exam
    input); `mode=STRIP_PROOF` strips only `#@ proof` clauses (used to put
    the golden baseline under identical, sidecar-free conditions)."""
    spec_lines = _spec_comment_lines(source)
    lines = source.split("\n")
    kept = [
        text for i, text in enumerate(lines, start=1)
        if i not in spec_lines
        or (mode == STRIP_PROOF and _clause_kind(text) != "proof")
    ]
    return "\n".join(kept)


def _code_line_index(source: str) -> dict[int, int]:
    """Source line number -> its index among NON-spec lines (1-based).

    The shared coordinate system: two sources that differ only in inserted
    `#@` lines agree on this index for every executable line.
    """
    spec_lines = _spec_comment_lines(source)
    index: dict[int, int] = {}
    seen = 0
    for lineno in range(1, len(source.split("\n")) + 1):
        if lineno in spec_lines:
            continue
        seen += 1
        index[lineno] = seen
    return index


def check_frozen(stripped: str, annotated: str
                 ) -> tuple[list[FreezeViolation], dict[int, int]]:
    """Verify the engine only INSERTED `#@` lines.

    Authoritative check: dropping full-line `#@` comments from `annotated`
    must reproduce `stripped` exactly, line for line — strictly stronger
    than AST equality (it also pins blank lines, whitespace, and comments,
    which AST equality would silently permit the engine to change). The AST
    comparison runs as a cross-check; any disagreement between the two is
    itself reported, since it means one of them is lying.

    Returns (violations, line_map) where line_map sends a STRIPPED line
    number to its line number in `annotated`.
    """
    violations: list[FreezeViolation] = []
    # Parse first: an unparseable answer is a syntax problem, and saying so
    # is more actionable than the tokenizer error stripping would raise.
    try:
        ast.parse(annotated)
    except SyntaxError as exc:
        return [FreezeViolation(
            exc.lineno or 0,
            f"annotated source does not parse: {exc.msg}")], {}
    try:
        annotated_code = strip_specs(annotated)
    except SpecExamError as exc:
        return [FreezeViolation(0, str(exc))], {}

    want = stripped.split("\n")
    got = annotated_code.split("\n")
    if want != got:
        for i, (a, b) in enumerate(zip(want, got), start=1):
            if a != b:
                violations.append(FreezeViolation(
                    i, f"executable line {i} changed: expected {a!r}, got {b!r}"))
                break
        else:
            violations.append(FreezeViolation(
                min(len(want), len(got)) + 1,
                f"executable line count changed: expected {len(want)} "
                f"line(s), got {len(got)}"))

    ast_equal = (ast.dump(ast.parse(stripped))
                 == ast.dump(ast.parse(annotated)))
    if ast_equal is False and not violations:
        # Text says unchanged, AST says otherwise — impossible unless a
        # check is wrong. Never silently trust the pair.
        violations.append(FreezeViolation(
            0, "internal: text-identical sources with differing ASTs"))
    if ast_equal is True and violations:
        violations.append(FreezeViolation(
            0, "note: the edit preserved the AST but changed source text "
               "(comments/blank lines/formatting are frozen too)"))

    line_map: dict[int, int] = {}
    if not violations:
        stripped_index = _code_line_index(stripped)
        annotated_index = _code_line_index(annotated)
        by_code_index = {v: k for k, v in annotated_index.items()}
        for src_line, code_index in stripped_index.items():
            if code_index in by_code_index:
                line_map[src_line] = by_code_index[code_index]
    return violations, line_map


def translate_equivalents(meta: dict[str, Any],
                          line_map: dict[int, int]) -> dict[str, Any]:
    """Rewrite line-numbered `equivalent_mutants` descriptions into the
    annotated file's numbering.

    Adjudicated equivalent mutants are recorded as e.g.
    ``"line 17: `>` -> `>=`"``. Inserting spec comments shifts those line
    numbers, so without translation the exclusion silently misses and the
    engine gets charged for a mutant the golden run was forgiven — the
    comparison breaks quietly, which is the worst way for it to break.
    """
    equivalents = meta.get("equivalent_mutants")
    if not equivalents:
        return meta
    translated: list[str] = []
    for description in equivalents:
        match = _EQUIV_LINE_RE.match(description)
        if match is None:
            translated.append(description)
            continue
        old = int(match.group(1))
        new = line_map.get(old)
        if new is None:
            # Unmappable: keep the original so the mismatch surfaces as an
            # un-excluded survivor rather than a silent exclusion.
            translated.append(description)
            continue
        translated.append(_EQUIV_LINE_RE.sub(f"line {new}: ", description, count=1))
    out = dict(meta)
    out["equivalent_mutants"] = translated
    return out


def build_spec_request(source: str, task_id: str, attempt: int,
                       errors: list[dict[str, Any]],
                       history: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": "lemmapy-specwrite-request/1",
        "rules": SPEC_RULES,
        "task": task_id,
        "attempt": attempt,
        "source": source,
        "errors": errors,
        "history": history,
        "reply_with": "Reply with the complete annotated file only.",
    }


@dataclass
class SpecExamScore:
    task_id: str
    valid: bool
    attempts: int
    reason: str
    height: int = 0
    mutants_total: int = 0
    mutants_killed: int = 0
    survivors: list[str] = field(default_factory=list)
    golden_height: int = 0
    golden_mutants_total: int = 0
    golden_mutants_killed: int = 0
    clause_counts: dict[str, int] = field(default_factory=dict)
    retry_reasons: list[str] = field(default_factory=list)
    wall_ms: int = 0
    usage: list[dict[str, Any] | None] = field(default_factory=list)

    @property
    def kill_rate(self) -> float | None:
        if not self.mutants_total:
            return None
        return self.mutants_killed / self.mutants_total

    @property
    def golden_kill_rate(self) -> float | None:
        if not self.golden_mutants_total:
            return None
        return self.golden_mutants_killed / self.golden_mutants_total


def _stage_scored_task(directory: Path, source: str,
                       meta: dict[str, Any]) -> Path:
    """A task dir holding exactly what the ladder should see: the source
    and its meta. No `.proofs.dfy` is ever staged — a stale sidecar would
    hand the scored run lemmas nobody earned."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "task.py").write_text(source)
    (directory / "meta.json").write_text(json.dumps(meta, indent=1))
    assert not (directory / "task.proofs.dfy").exists()
    return directory


def _clause_counts(source: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for lineno in sorted(_spec_comment_lines(source)):
        kind = _clause_kind(source.split("\n")[lineno - 1]) or "?"
        counts[kind] = counts.get(kind, 0) + 1
    return counts


def _validate(stripped: str, proposal: str) -> list[dict[str, Any]]:
    """Mechanical validity only — never a verification outcome."""
    errors: list[dict[str, Any]] = []
    try:
        ast.parse(proposal)
    except SyntaxError as exc:
        return [{"kind": "syntax", "line": exc.lineno,
                 "message": f"the file does not parse: {exc.msg}"}]
    try:
        violations, _ = check_frozen(stripped, proposal)
    except SpecExamError as exc:
        return [{"kind": "freeze", "line": None, "message": str(exc)}]
    errors += [{"kind": "freeze", "line": v.line, "message": v.message}
               for v in violations]
    if errors:
        return errors
    specs = parse_source(proposal)
    for spec in specs.functions:
        for clause in spec.clauses:
            if clause.error:
                errors.append({"kind": "spec", "line": clause.line,
                               "message": clause.error})
            elif clause.kind == "proof":
                errors.append({
                    "kind": "spec", "line": clause.line,
                    "message": "`#@ proof` clauses are not allowed in this "
                               "exam (there is no lemma sidecar)"})
    for orphan in specs.orphans:
        errors.append({"kind": "spec", "line": orphan.line,
                       "message": orphan.error or "orphan spec comment"})
    if errors:
        return errors
    has_ensures = any(c.kind == "ensures" for s in specs.functions
                      for c in s.clauses)
    if not has_ensures:
        errors.append({
            "kind": "spec", "line": None,
            "message": "no `#@ ensures` clause anywhere — a specification "
                       "must say what the function computes"})
    return errors


def _golden_baseline(task_dir: Path, workdir: Path, cache_dir: Path,
                     ladder_kwargs: dict[str, Any]) -> TaskScore:
    """Score the golden task under EXAM CONDITIONS: its `#@ proof` clauses
    stripped and no sidecar staged, so the engine is not being compared
    against a run that had lemmas available. Cached by (source, settings)
    so a trial matrix pays for it once."""
    golden_source = (task_dir / "task.py").read_text()
    meta_path = task_dir / "meta.json"
    meta = json.loads(meta_path.read_text()) if meta_path.exists() else {}
    exam_source = strip_specs(golden_source, mode=STRIP_PROOF)
    key = hashlib.sha256(
        (exam_source + repr(sorted(ladder_kwargs.items()))).encode()
    ).hexdigest()[:16]
    cache_file = cache_dir / f"{task_dir.name}-{key}.json"
    if cache_file.exists():
        cached = json.loads(cache_file.read_text())
        score = TaskScore(task_id=task_dir.name)
        score.mutants_total = cached["mutants_total"]
        score.mutants_killed = cached["mutants_killed"]
        score.survivors = cached["survivors"]
        score._cached_height = cached["height"]  # type: ignore[attr-defined]
        return score
    staged = _stage_scored_task(workdir / "golden-src", exam_source, meta)
    score = run_task(staged, workdir / "golden-ladder", **ladder_kwargs)
    cache_dir.mkdir(parents=True, exist_ok=True)
    cache_file.write_text(json.dumps({
        "height": score.height, "mutants_total": score.mutants_total,
        "mutants_killed": score.mutants_killed, "survivors": score.survivors,
    }, indent=1))
    return score


def _height_of(score: TaskScore) -> int:
    return getattr(score, "_cached_height", None) or score.height


def spec_exam_tasks(tasks_root: Path) -> list[Path]:
    return sorted(p.parent for p in tasks_root.glob("*/task.py"))


def run_spec_exam(tasks_root: Path, workdir: Path,
                  engine_factory: Callable[[], Engine],
                  retries: int = 2, only: set[str] | None = None,
                  **ladder_kwargs: Any) -> list[SpecExamScore]:
    scores: list[SpecExamScore] = []
    cache_dir = workdir / "_golden-cache"
    for task_dir in spec_exam_tasks(tasks_root):
        task_id = task_dir.name
        if only is not None and task_id not in only:
            continue
        exam_dir = prepare_exam_workspace(tasks_root, workdir, task_id)
        golden_source = (task_dir / "task.py").read_text()
        meta_path = task_dir / "meta.json"
        meta = json.loads(meta_path.read_text()) if meta_path.exists() else {}
        stripped = strip_specs(golden_source)
        (exam_dir / "stripped.py").write_text(stripped)

        golden = _golden_baseline(task_dir, exam_dir, cache_dir, ladder_kwargs)
        engine = engine_factory()
        t0 = time.monotonic()
        errors: list[dict[str, Any]] = []
        history: list[dict[str, Any]] = []
        retry_reasons: list[str] = []
        proposal = ""
        attempt = 0
        for attempt in range(retries + 1):
            request = build_spec_request(stripped, task_id, attempt, errors,
                                         history)
            try:
                proposal = _strip_fences(engine(request))
            except Exception as exc:
                errors = [{"kind": "engine", "line": None,
                           "message": f"engine error: {exc}"}]
                break
            (exam_dir / f"attempt{attempt}.py").write_text(proposal)
            errors = _validate(stripped, proposal)
            if not errors:
                break
            retry_reasons.append(errors[0]["kind"])
            history.append({"attempt": attempt,
                            "errors": [e["kind"] for e in errors]})

        wall_ms = int((time.monotonic() - t0) * 1000)
        usage = list(getattr(engine, "usage_log", []))
        if errors:
            scores.append(SpecExamScore(
                task_id=task_id, valid=False, attempts=attempt + 1,
                reason=f"{errors[0]['kind']}: {errors[0]['message'][:120]}",
                golden_height=_height_of(golden),
                golden_mutants_total=golden.mutants_total,
                golden_mutants_killed=golden.mutants_killed,
                retry_reasons=retry_reasons, wall_ms=wall_ms, usage=usage))
            continue

        _, line_map = check_frozen(stripped, proposal)
        staged = _stage_scored_task(exam_dir / "scored", proposal,
                                    translate_equivalents(meta, line_map))
        scored = run_task(staged, exam_dir / "ladder", **ladder_kwargs)
        scores.append(SpecExamScore(
            task_id=task_id, valid=True, attempts=attempt + 1,
            reason="scored", height=scored.height,
            mutants_total=scored.mutants_total,
            mutants_killed=scored.mutants_killed,
            survivors=scored.survivors,
            golden_height=_height_of(golden),
            golden_mutants_total=golden.mutants_total,
            golden_mutants_killed=golden.mutants_killed,
            clause_counts=_clause_counts(proposal),
            retry_reasons=retry_reasons, wall_ms=wall_ms, usage=usage))
    return scores


def render_spec_exam_report(scores: list[SpecExamScore]) -> str:
    if not scores:
        return "spec-writing exam: no tasks to examine"
    header = (f"{'task':<22} {'valid':<6} {'height':<8} {'kill':<9} "
              f"{'golden-kill':<12} {'attempts':<9} clauses")
    lines = [header, "-" * len(header)]
    for s in scores:
        if not s.valid:
            lines.append(f"{s.task_id:<22} {'NO':<6} {'-':<8} {'-':<9} "
                         f"{f'{s.golden_mutants_killed}/{s.golden_mutants_total}':<12} "
                         f"{s.attempts:<9} {s.reason[:40]}")
            continue
        kill = f"{s.mutants_killed}/{s.mutants_total}" if s.mutants_total else "-"
        golden_kill = (f"{s.golden_mutants_killed}/{s.golden_mutants_total}"
                       if s.golden_mutants_total else "-")
        clauses = ", ".join(f"{k}:{v}" for k, v in sorted(s.clause_counts.items()))
        lines.append(f"{s.task_id:<22} {'yes':<6} "
                     f"{f'{s.height}/{s.golden_height}':<8} {kill:<9} "
                     f"{golden_kill:<12} {s.attempts:<9} {clauses}")
    valid = [s for s in scores if s.valid]
    killed = sum(s.mutants_killed for s in valid)
    total = sum(s.mutants_total for s in valid)
    g_killed = sum(s.golden_mutants_killed for s in scores)
    g_total = sum(s.golden_mutants_total for s in scores)
    lines.append("-" * len(header))
    lines.append(f"valid: {len(valid)}/{len(scores)}")
    lines.append(
        f"spec strength: engine {killed}/{total}"
        + (f" ({100 * killed / total:.0f}%)" if total else "")
        + f" vs golden {g_killed}/{g_total}"
        + (f" ({100 * g_killed / g_total:.0f}%)" if g_total else "")
        + "   [heights are out of the golden's exam-conditions height:"
          " no sidecar, `#@ proof` stripped]")
    return "\n".join(lines)


def spec_scores_to_json(scores: list[SpecExamScore]) -> dict[str, Any]:
    return {
        "schema": "lemmapy-specwrite-scores/1",
        "tasks": [
            {
                "id": s.task_id, "valid": s.valid, "attempts": s.attempts,
                "reason": s.reason, "height": s.height,
                "mutants": {"total": s.mutants_total, "killed": s.mutants_killed,
                            "survivors": s.survivors},
                "golden": {"height": s.golden_height,
                           "mutants_total": s.golden_mutants_total,
                           "mutants_killed": s.golden_mutants_killed},
                "clause_counts": s.clause_counts,
                "retry_reasons": s.retry_reasons,
                "wall_ms": s.wall_ms, "usage": s.usage,
            }
            for s in scores
        ],
    }
