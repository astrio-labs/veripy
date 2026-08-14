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
        if not loops:
            return None
        has_invariant = any(
            c.kind == "invariant"
            for spec in getattr(specs, "functions", [])
            if spec.name == fn.name
            for c in spec.clauses)
        if not has_invariant:
            return (f"`{fn.name}` contains a loop with no `#@ invariant`. A "
                    f"postcondition about a value the loop builds usually "
                    f"needs one: state what is true of that value on every "
                    f"iteration, as the first line inside the loop body.")
        return ("an invariant is present but did not carry the "
                "postcondition — it may need to be strengthened to mention "
                "the value the ensures talks about.")

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
