"""Fixits for PROOF failures, not just conformance rejections.

The diagnostics pass gave every conformance rejection a "outside the
fragment because X, try Y" message. Proof failures never got the same
treatment, and a feedback-sufficiency exercise showed what that costs: an
unannotated in-fragment function was taken to `verified` using tool output
alone, and the one place the tools ran out was here. Asked to prove a
postcondition over a loop, `lemmapy verify` said:

    a postcondition could not be proved on this return path (related: line 1)

which names the symptom precisely and the remedy not at all. The missing
ingredient was a single `#@ invariant` line — highly predictable from the
shape of the failure, since a function whose loop carries NO invariant
almost never proves a non-trivial postcondition.

These hints are deliberately conservative: they fire only when the shape
is unambiguous, and they suggest a mechanism rather than writing the
specification for you (which would be guessing at intent).
"""

from __future__ import annotations

import ast
from typing import Any


def _enclosing_function(tree: ast.Module, line: int) -> ast.FunctionDef | None:
    best = None
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.lineno <= line:
            end = node.end_lineno or node.lineno
            if line <= end:
                return node
            best = node
    return best


def _loops_in(fn: ast.FunctionDef) -> list[ast.stmt]:
    return [n for n in ast.walk(fn) if isinstance(n, (ast.For, ast.While))]


def _owning_loop(loops: list[ast.stmt], line: int) -> ast.stmt | None:
    """The loop whose body `line` sits in, innermost first.

    Ownership, not mere presence, is what the postcondition hint needs: an
    invariant written on an inner loop says nothing about whether the outer
    one carries its own, and crediting it to the outer loop would send the
    reader to strengthen a clause that is not the missing ingredient.
    Mirrors the containment rule `extract` uses to bind body clauses to
    their function (`lineno < line <= end_lineno`).
    """
    best = None
    for loop in loops:
        end = loop.end_lineno or loop.lineno
        if loop.lineno < line <= end:
            if best is None or loop.lineno > best.lineno:
                best = loop
    return best


def proof_hint(diagnostic: Any, source: str, specs: Any) -> str | None:
    """A one-line remedy for this diagnostic, or None when the shape is
    not unambiguous enough to advise."""
    kind = getattr(diagnostic, "obligation", None)
    line = getattr(diagnostic, "py_line", None)
    if kind is None or line is None:
        return None
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return None
    fn = _enclosing_function(tree, line)
    if fn is None:
        return None

    if kind == "postcondition":
        loops = _loops_in(fn)
        # Only loops that could have run before this return are on the path
        # that failed. A loop further down the function cannot be why THIS
        # return path did not prove, and an early return that precedes every
        # loop has some other cause entirely.
        on_path = [n for n in loops if n.lineno <= line]
        if not on_path:
            return None
        # Per-loop, not per-function. Asking only whether the function has an
        # invariant ANYWHERE means an invariant on the first of two loops
        # answers for a failure arising from the second, and the reader is
        # told to strengthen a clause they already wrote when the missing
        # ingredient is to ADD one to the bare loop — the wrong edit, from
        # the module written to stop exactly that.
        owners = set()
        for spec in getattr(specs, "functions", []):
            if spec.name != fn.name:
                continue
            for c in spec.clauses:
                if c.kind == "invariant":
                    owner = _owning_loop(loops, c.line)
                    if owner is not None:
                        owners.add(id(owner))
        bare = [n for n in on_path if id(n) not in owners]
        if bare:
            first = min(bare, key=lambda n: n.lineno)
            return (f"the loop at line {first.lineno} in `{fn.name}` carries "
                    f"no `#@ invariant`. A postcondition about a value that "
                    f"loop builds usually needs one: state what is true of "
                    f"that value on every iteration, as the first line inside "
                    f"the loop body.")
        return ("every loop on this path has an invariant, but they did not "
                "carry the postcondition — one may need to be strengthened "
                "to mention the value the ensures talks about.")

    if kind == "invariant":
        return ("a loop invariant failed. Dafny checks it on ENTRY and after "
                "every iteration, so it must hold before the loop runs too "
                "— an off-by-one in the bound is the usual cause.")

    if kind == "call-precondition":
        return ("a callee's `requires` was not established. If the callee is "
                "a preamble function this is its domain condition (e.g. a "
                "non-empty sequence for `max`), so guard the call or add a "
                "`#@ requires` that rules the case out.")

    if kind == "termination":
        return ("add a `#@ decreases <expr>` naming a quantity that strictly "
                "decreases and is bounded below.")

    if kind == "resolution":
        return ("the proof sidecar does not typecheck, so the proof was "
                "never attempted — fix the declaration against the preamble "
                "signatures rather than strengthening the proof.")

    return None
