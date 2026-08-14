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


def _spec_comments(source: str) -> dict[int, tuple[int, str]]:
    """Map line number -> (column, comment text) for every spec comment."""
    comments: dict[int, tuple[int, str]] = {}
    tokens = tokenize.generate_tokens(io.StringIO(source).readline)
    for tok in tokens:
        if tok.type == tokenize.COMMENT and tok.string.startswith("#@"):
            comments[tok.start[0]] = (tok.start[1], tok.string[2:].strip())
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


RESERVED_PARAMS = frozenset({"result", "OLD"})


def _safe_params(node: ast.FunctionDef) -> tuple[tuple[str, ...], str | None]:
    """Named parameters plus a fragment diagnostic (None if the signature is fine).

    A bad signature only matters for functions that carry specs — unannotated
    variadic helpers elsewhere in the module must not abort processing.
    """
    a = node.args
    names = tuple(p.arg for p in (*a.posonlyargs, *a.args, *a.kwonlyargs))
    if a.vararg or a.kwarg:
        return names, "*args/**kwargs are outside the fragment"
    reserved = [n for n in names if n in RESERVED_PARAMS]
    if reserved:
        return names, (
            f"parameter name(s) {', '.join(reserved)} collide with the spec "
            f"language (`result` and `OLD` are reserved); rename the parameter"
        )
    return names, None


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


def spec_comment_sites(source: str, kind: str) -> dict[int, int]:
    """line -> column of every spec comment this extractor reads as `kind`.

    Anything that REMOVES clauses (the exam screen strips `proof`) has to
    agree with the tokenizer that reads them, or it edits a different
    language than the parser does: `#@proof`, `#@  proof` and a trailing
    `y = x  #@ proof L()` are all clauses of kind `proof`, while a line
    reading `#@ proof ...` inside a string literal is not one at all.
    """
    return {line: col for line, (col, text) in _spec_comments(source).items()
            if _split_kind(text)[0] == kind}


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
    signature_errors: dict[int, str] = {}  # index into specs -> diagnostic

    for index, node in enumerate(functions):
        anchor = node.decorator_list[0].lineno if node.decorator_list else node.lineno
        params, params_error = _safe_params(node)
        if params_error is not None:
            signature_errors[index] = params_error
        spec = FunctionSpec(
            name=node.name,
            lineno=node.lineno,
            anchor_lineno=anchor,
            params=params,
        )
        # Contract block: walk upward from the line above the anchor.
        block: list[tuple[int, int, str]] = []
        line = anchor - 1
        while line in comments:
            ccol, ctext = comments[line]
            block.append((line, ccol, ctext))
            line -= 1
        for cline, ccol, text in reversed(block):
            consumed.add(cline)
            kind, rest = _split_kind(text)
            if kind not in CLAUSE_KINDS:
                clause = Clause(
                    kind=kind or "?", raw=rest, line=cline,
                    error=f"unknown clause {kind!r} (expected one of {', '.join(CLAUSE_KINDS)})",
                )
            elif kind not in HEADER_KINDS:
                clause = Clause(
                    kind=kind, raw=rest, line=cline,
                    error=f"`{kind}` belongs inside a loop body, not the contract block",
                )
            else:
                clause = parse_clause(kind, rest, cline, params, module_names)
            clause.col = ccol
            spec.clauses.append(clause)
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
        ccol, text = comments[cline]
        kind, rest = _split_kind(text)
        hit = innermost(cline)
        if hit is None:
            clause = Clause(
                kind=kind or "?", raw=rest, line=cline,
                error="spec comment is not attached to any function "
                      "(contract blocks must sit directly above a `def`)",
            )
            clause.col = ccol
            orphans.append(clause)
            continue
        node, spec = hit
        if kind not in CLAUSE_KINDS:
            clause = Clause(
                kind=kind or "?", raw=rest, line=cline,
                error=f"unknown clause {kind!r} (expected one of {', '.join(CLAUSE_KINDS)})",
            )
        elif kind not in BODY_KINDS:
            clause = Clause(
                kind=kind, raw=rest, line=cline,
                error=f"`{kind}` belongs in the contract block directly above the `def`",
            )
        else:
            clause = parse_clause(
                kind, rest, cline, spec.params, module_names,
                extra_names=_local_names(node),
            )
        clause.col = ccol
        spec.clauses.append(clause)

    # A bad signature is an error only on functions that actually carry specs.
    for index, message in signature_errors.items():
        spec = specs[index]
        if spec.clauses:
            spec.clauses.append(Clause(
                kind="signature", raw=spec.name, line=spec.lineno, error=message,
            ))

    for spec in specs:
        spec.clauses.sort(key=lambda c: c.line)
    return ModuleSpecs(functions=[s for s in specs if s.clauses], orphans=orphans)
