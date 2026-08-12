"""Parsing and desugaring of ``#@`` spec expressions (grammar v0).

The spec expression language is Python's expression grammar extended with:

    forall X in D[, Y in E ...] :: BODY   ->  all((BODY) for X in (D) ...)
    exists X in D[, Y in E ...] :: BODY   ->  any((BODY) for X in (D) ...)
    A ==> B                               ->  (not (A)) or (B)   (right-assoc)
    result                                    (ensures only)
    old(param)                                (ensures only)

Desugared clauses must parse with ``ast.parse(mode="eval")``. The grammar and
its decisions live in SPEC-GRAMMAR.md; changes land there first.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field

CLAUSE_KINDS = ("verified", "requires", "ensures", "invariant", "decreases")
HEADER_KINDS = ("verified", "requires", "ensures", "decreases")
BODY_KINDS = ("invariant", "decreases")

RESERVED = frozenset({"forall", "exists", "result", "old", "mutates", "extern"})

SAFE_BUILTINS = frozenset({
    "len", "range", "all", "any", "min", "max", "sum", "abs", "sorted",
    "enumerate", "zip", "reversed", "set", "list", "tuple", "dict",
    "int", "bool", "float", "str", "isinstance", "divmod", "round",
})

_OPEN = "([{"
_CLOSE = ")]}"
_QUANT_RE = re.compile(r"^\s*(forall|exists)\b(.*)$", re.S)
_BINDER_RE = re.compile(r"^\s*([A-Za-z_]\w*)\s+in\s+(.+)$", re.S)
_OLD_RE = re.compile(r"\bold\(\s*([A-Za-z_]\w*)\s*\)")


class SpecError(Exception):
    """A spec clause the grammar rejects; message is the diagnostic."""


def _split_top_once(s: str, sep: str) -> tuple[str, str] | None:
    """Split at the first occurrence of `sep` outside brackets and strings."""
    depth = 0
    quote: str | None = None
    i = 0
    while i < len(s):
        c = s[i]
        if quote is not None:
            if c == "\\":
                i += 2
                continue
            if c == quote:
                quote = None
        elif c in "\"'":
            quote = c
        elif c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            return s[:i], s[i + len(sep):]
        i += 1
    return None


def _split_top_all(s: str, sep: str) -> list[str]:
    parts = []
    rest = s
    while True:
        split = _split_top_once(rest, sep)
        if split is None:
            parts.append(rest)
            return parts
        parts.append(split[0])
        rest = split[1]


def _matching_bracket(s: str, i: int) -> int:
    close_for = dict(zip(_OPEN, _CLOSE))
    want = close_for[s[i]]
    depth = 0
    quote: str | None = None
    j = i
    while j < len(s):
        c = s[j]
        if quote is not None:
            if c == "\\":
                j += 2
                continue
            if c == quote:
                quote = None
        elif c in "\"'":
            quote = c
        elif c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth -= 1
            if depth == 0:
                if c != want:
                    raise SpecError(f"mismatched brackets: expected {want!r}, found {c!r}")
                return j
        j += 1
    raise SpecError("unbalanced brackets in spec expression")


def _rewrite_groups(s: str) -> str:
    """Desugar the inside of every bracketed group; leave the rest as-is."""
    out: list[str] = []
    quote: str | None = None
    i = 0
    while i < len(s):
        c = s[i]
        if quote is not None:
            out.append(c)
            if c == "\\" and i + 1 < len(s):
                out.append(s[i + 1])
                i += 2
                continue
            if c == quote:
                quote = None
            i += 1
            continue
        if c in "\"'":
            quote = c
            out.append(c)
            i += 1
            continue
        if c in _OPEN:
            j = _matching_bracket(s, i)
            inner = s[i + 1:j]
            out.append(c + (desugar(inner) if inner.strip() else inner) + s[j])
            i = j + 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def desugar(src: str) -> str:
    """Rewrite grammar-v0 spec syntax into plain Python expression source."""
    s = src.strip()
    if not s:
        raise SpecError("empty spec expression")

    m = _QUANT_RE.match(s)
    if m:
        keyword, rest = m.group(1), m.group(2)
        split = _split_top_once(rest, "::")
        if split is None:
            raise SpecError(
                f"'{keyword}' needs '::' between its binders and its body "
                f"(e.g. `{keyword} i in range(n) :: ...`)"
            )
        header, body = split
        binders: list[tuple[str, str]] = []
        for part in _split_top_all(header, ","):
            bm = _BINDER_RE.match(part.strip())
            if bm is None:
                raise SpecError(
                    f"bad binder {part.strip()!r}: expected `name in <iterable>` "
                    f"(quantifier domains are explicit in v0, see SPEC-GRAMMAR.md)"
                )
            var, domain = bm.group(1), bm.group(2).strip()
            if var in RESERVED:
                raise SpecError(f"{var!r} is a reserved word and cannot be a binder")
            binders.append((var, desugar(domain)))
        inner = desugar(body)
        gens = " ".join(f"for {var} in ({dom})" for var, dom in binders)
        fn = "all" if keyword == "forall" else "any"
        return f"{fn}(({inner}) {gens})"

    split = _split_top_once(s, "==>")
    if split is not None:
        left, right = split
        return f"(not ({desugar(left)})) or ({desugar(right)})"

    return _rewrite_groups(s)


@dataclass
class Clause:
    kind: str
    raw: str  # text after the kind keyword, as written
    line: int
    desugared: str | None = None
    error: str | None = None
    old_names: tuple[str, ...] = ()


@dataclass
class FunctionSpec:
    name: str
    lineno: int  # line of the `def`
    anchor_lineno: int  # line of the first decorator, or the `def`
    params: tuple[str, ...]
    clauses: list[Clause] = field(default_factory=list)

    @property
    def verified(self) -> bool:
        return any(c.kind == "verified" for c in self.clauses)

    @property
    def errors(self) -> list[Clause]:
        return [c for c in self.clauses if c.error is not None]

    def by_kind(self, kind: str) -> list[Clause]:
        return [c for c in self.clauses if c.kind == kind and c.error is None]


@dataclass
class ModuleSpecs:
    functions: list[FunctionSpec]
    orphans: list[Clause]  # #@ comments not attached to any function

    @property
    def errors(self) -> list[Clause]:
        errs = [c for f in self.functions for c in f.errors]
        errs += [c for c in self.orphans if c.error is not None]
        return errs


def _bound_names(tree: ast.AST) -> set[str]:
    bound: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.comprehension):
            for t in ast.walk(node.target):
                if isinstance(t, ast.Name):
                    bound.add(t.id)
        elif isinstance(node, ast.Lambda):
            bound.update(a.arg for a in node.args.args)
    return bound


def parse_clause(
    kind: str,
    text: str,
    line: int,
    params: tuple[str, ...],
    module_names: frozenset[str],
    extra_names: frozenset[str] = frozenset(),
) -> Clause:
    clause = Clause(kind=kind, raw=text, line=line)
    if kind == "verified":
        if text.strip():
            clause.error = "`#@ verified` takes no expression"
        return clause
    try:
        desugared = desugar(text)
        tree = ast.parse(desugared, mode="eval")
    except SpecError as exc:
        clause.error = str(exc)
        return clause
    except SyntaxError as exc:
        clause.error = f"not a valid spec expression after desugaring ({exc.msg}): {desugared!r}"
        return clause

    old_names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "old":
            if kind != "ensures":
                clause.error = "`old(...)` is only meaningful in `ensures`"
                return clause
            if (
                len(node.args) != 1
                or node.keywords
                or not isinstance(node.args[0], ast.Name)
            ):
                clause.error = "`old(...)` takes a single bare parameter name in v0"
                return clause
            arg = node.args[0].id
            if arg not in params:
                clause.error = f"`old({arg})`: {arg!r} is not a parameter"
                return clause
            old_names.append(arg)

    names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
    if "result" in names and kind != "ensures":
        clause.error = "`result` is only meaningful in `ensures`"
        return clause
    allowed = set(params) | SAFE_BUILTINS | set(module_names) | set(extra_names) | _bound_names(tree)
    if kind == "ensures":
        allowed |= {"result", "old"}
    unknown = sorted(names - allowed)
    if unknown:
        clause.error = f"unknown name(s) in spec: {', '.join(unknown)}"
        return clause

    clause.desugared = desugared
    clause.old_names = tuple(dict.fromkeys(old_names))
    return clause
