"""Extract ``#@`` spec comments from source and attach them to functions.

Association rules (grammar v0, SPEC-GRAMMAR.md):
- The *contract block* is the contiguous run of ``#@`` comment lines ending on
  the line directly above the ``def`` (or its first decorator).
- ``invariant`` / ``decreases`` comments inside a function body attach to the
  innermost function containing them.
- Anything else is an orphan and reported as an error.
"""

from __future__ import annotations

import ast
import io
import tokenize

from .parse import (
    BODY_KINDS,
    CLAUSE_KINDS,
    HEADER_KINDS,
    Clause,
    FunctionSpec,
    ModuleSpecs,
    parse_clause,
)


def _spec_comments(source: str) -> dict[int, str]:
    """Map line number -> comment text (after '#@') for every spec comment."""
    comments: dict[int, str] = {}
    tokens = tokenize.generate_tokens(io.StringIO(source).readline)
    for tok in tokens:
        if tok.type == tokenize.COMMENT and tok.string.startswith("#@"):
            comments[tok.start[0]] = tok.string[2:].strip()
    return comments


def _module_names(module: ast.Module) -> frozenset[str]:
    names: set[str] = set()
    for node in module.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                for t in ast.walk(target):
                    if isinstance(t, ast.Name):
                        names.add(t.id)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            names.add(node.target.id)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                names.add((alias.asname or alias.name).split(".")[0])
    return frozenset(names)


def _params(node: ast.FunctionDef) -> tuple[str, ...]:
    a = node.args
    if a.vararg or a.kwarg:
        # Outside the fragment; the conformance checker owns this later.
        raise ValueError(f"{node.name}: *args/**kwargs are outside the fragment")
    return tuple(p.arg for p in (*a.posonlyargs, *a.args, *a.kwonlyargs))


def _local_names(node: ast.FunctionDef) -> frozenset[str]:
    """Names assigned anywhere in the function body (loop invariants may use them)."""
    return frozenset(
        n.id for n in ast.walk(node)
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)
    )


def _split_kind(text: str) -> tuple[str, str]:
    parts = text.split(None, 1)
    kind = parts[0] if parts else ""
    rest = parts[1] if len(parts) > 1 else ""
    return kind, rest


def parse_source(source: str, filename: str = "<string>") -> ModuleSpecs:
    module = ast.parse(source, filename=filename)
    comments = _spec_comments(source)
    module_names = _module_names(module)

    functions = [
        n for n in ast.walk(module)
        if isinstance(n, ast.FunctionDef)
    ]
    consumed: set[int] = set()
    specs: list[FunctionSpec] = []

    for node in functions:
        anchor = node.decorator_list[0].lineno if node.decorator_list else node.lineno
        params = _params(node)
        spec = FunctionSpec(
            name=node.name,
            lineno=node.lineno,
            anchor_lineno=anchor,
            params=params,
        )
        # Contract block: walk upward from the line above the anchor.
        block: list[tuple[int, str]] = []
        line = anchor - 1
        while line in comments:
            block.append((line, comments[line]))
            line -= 1
        for cline, text in reversed(block):
            consumed.add(cline)
            kind, rest = _split_kind(text)
            if kind not in CLAUSE_KINDS:
                spec.clauses.append(Clause(
                    kind=kind or "?", raw=rest, line=cline,
                    error=f"unknown clause {kind!r} (expected one of {', '.join(CLAUSE_KINDS)})",
                ))
            elif kind not in HEADER_KINDS:
                spec.clauses.append(Clause(
                    kind=kind, raw=rest, line=cline,
                    error=f"`{kind}` belongs inside a loop body, not the contract block",
                ))
            else:
                spec.clauses.append(parse_clause(kind, rest, cline, params, module_names))
        specs.append(spec)

    # Body comments: attach to the innermost containing function.
    def innermost(line: int) -> tuple[ast.FunctionDef, FunctionSpec] | None:
        best: tuple[int, ast.FunctionDef, FunctionSpec] | None = None
        for node, spec in zip(functions, specs):
            end = node.end_lineno or node.lineno
            if node.lineno < line <= end:
                span = end - node.lineno
                if best is None or span < best[0]:
                    best = (span, node, spec)
        return (best[1], best[2]) if best else None

    orphans: list[Clause] = []
    for cline in sorted(set(comments) - consumed):
        text = comments[cline]
        kind, rest = _split_kind(text)
        hit = innermost(cline)
        if hit is None:
            orphans.append(Clause(
                kind=kind or "?", raw=rest, line=cline,
                error="spec comment is not attached to any function "
                      "(contract blocks must sit directly above a `def`)",
            ))
            continue
        node, spec = hit
        if kind not in CLAUSE_KINDS:
            spec.clauses.append(Clause(
                kind=kind or "?", raw=rest, line=cline,
                error=f"unknown clause {kind!r} (expected one of {', '.join(CLAUSE_KINDS)})",
            ))
        elif kind not in BODY_KINDS:
            spec.clauses.append(Clause(
                kind=kind, raw=rest, line=cline,
                error=f"`{kind}` belongs in the contract block directly above the `def`",
            ))
        else:
            spec.clauses.append(parse_clause(
                kind, rest, cline, spec.params, module_names,
                extra_names=_local_names(node),
            ))

    for spec in specs:
        spec.clauses.sort(key=lambda c: c.line)
    return ModuleSpecs(functions=[s for s in specs if s.clauses], orphans=orphans)
