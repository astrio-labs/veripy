"""Deterministic mutant generation for veripy-benchmark spec-strength scoring.

Each mutant is ONE small, plausible bug spliced into the original source
TEXT (not unparsed AST — the `#@` spec comments must survive verbatim).

A mutant's description is its IDENTITY: `meta.json` adjudicates equivalent
mutants by exact string match, so the description must name exactly one
fault. It therefore carries the column as well as the line — two mutation
sites of the same kind on one line would otherwise share a label, and a
single adjudication would silently retire both.
Generation is deterministic: an ordered AST walk, no randomness, so a
task's mutant panel is stable across runs and machines.

A strong spec kills every non-equivalent mutant (CrossHair finds a
counterexample); a surviving mutant is either a spec gap or an equivalent
mutant — both worth human eyes, which is why survivors are reported
individually.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass

_CMP_SWAPS: dict[type, type] = {
    ast.Lt: ast.LtE, ast.LtE: ast.Lt,
    ast.Gt: ast.GtE, ast.GtE: ast.Gt,
    ast.Eq: ast.NotEq, ast.NotEq: ast.Eq,
}
_CMP_TEXT = {
    ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">=",
    ast.Eq: "==", ast.NotEq: "!=",
}
_ARITH_SWAPS = {ast.Add: "-", ast.Sub: "+"}


@dataclass(frozen=True)
class Mutation:
    line: int  # 1-based
    col: int
    end_col: int
    replacement: str
    description: str
    family: str = "operator"


def _param_groups(fn: ast.FunctionDef) -> dict[str, list[str]]:
    """Parameters grouped by annotation text.

    Operand replacement swaps a parameter for another of the SAME declared
    type: always in scope (so no NameError masquerading as a fault) and
    type-compatible (so no TypeError either) — the mutant is a genuine
    wrong-variable bug, which is what the operator is for.
    """
    groups: dict[str, list[str]] = {}
    args = fn.args
    for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs):
        if arg.annotation is None:
            continue
        groups.setdefault(ast.unparse(arg.annotation), []).append(arg.arg)
    return {k: v for k, v in groups.items() if len(v) > 1}


def _operand_mutations(tree: ast.Module) -> list[Mutation]:
    """Replace a parameter read with another parameter of the same type.

    The panel's five operator families all perturb an OPERATOR; none
    perturbs an OPERAND, so a specification that never says which input the
    result depends on scores full marks. `clamp`'s golden spec is the
    corpus's own counterexample: drop its value-pinning clause and the
    weakened spec — satisfied by `return lo`, ignoring the input entirely —
    was indistinguishable from golden until this family existed.
    """
    out: list[Mutation] = []
    for fn in ast.walk(tree):
        if not isinstance(fn, ast.FunctionDef):
            continue
        groups = _param_groups(fn)
        if not groups:
            continue
        by_name = {name: group for group in groups.values() for name in group}
        for node in ast.walk(fn):
            if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
                continue
            if node.lineno != node.end_lineno or node.id not in by_name:
                continue
            for other in by_name[node.id]:
                if other == node.id:
                    continue
                out.append(Mutation(
                    node.lineno, node.col_offset, node.end_col_offset, other,
                    f"line {node.lineno} col {node.col_offset}: "
                    f"`{node.id}` -> `{other}`",
                    family="operand",
                ))
    return out


def _select(mutations: list[Mutation], cap: int) -> list[Mutation]:
    """Cap the panel by round-robin across families, not by position.

    A plain positional prefix makes the panel a *line-prefix* of the
    function: `is_prime` hit the old cap exactly, so its panel silently
    became "the first 8 sites in line order" and the later half of the
    function went unprobed. Round-robin keeps every family represented at
    any cap, and stays deterministic (families and members are sorted).
    """
    by_family: dict[str, list[Mutation]] = {}
    for m in mutations:
        by_family.setdefault(m.family, []).append(m)
    for family in by_family:
        by_family[family].sort(key=lambda m: (m.line, m.col, m.replacement))
    picked: list[Mutation] = []
    index = 0
    while len(picked) < cap:
        added = False
        for family in sorted(by_family):
            members = by_family[family]
            if index < len(members):
                picked.append(members[index])
                added = True
                if len(picked) >= cap:
                    break
        if not added:
            break
        index += 1
    return sorted(picked, key=lambda m: (m.line, m.col, m.replacement))


def _splice(source_lines: list[str], m: Mutation) -> str:
    lines = list(source_lines)
    row = lines[m.line - 1]
    lines[m.line - 1] = row[: m.col] + m.replacement + row[m.end_col:]
    return "\n".join(lines) + "\n"


def _op_span(node: ast.expr, left: ast.expr, right: ast.expr,
             source_lines: list[str], token: str) -> tuple[int, int, int] | None:
    """Locate an operator token between two same-line operands."""
    if left.end_lineno != left.lineno or left.lineno != right.lineno:
        return None
    row = source_lines[left.lineno - 1]
    start = left.end_col_offset
    end = right.col_offset
    idx = row.find(token, start, end)
    if idx < 0:
        return None
    return left.lineno, idx, idx + len(token)


def generate_mutations(source: str, max_mutants: int = 16) -> list[tuple[str, str]]:
    """Return up to `max_mutants` (description, mutated_source) pairs.
    Mutations only touch executable code — spec comments are untouched by
    construction (they are comments; the AST never sees them)."""
    tree = ast.parse(source)
    source_lines = source.split("\n")
    mutations: list[Mutation] = []

    for node in ast.walk(tree):
        match node:
            case ast.Compare(left=left, ops=[op], comparators=[comp]) \
                    if type(op) in _CMP_SWAPS:
                token = _CMP_TEXT[type(op)]
                span = _op_span(node, left, comp, source_lines, token)
                if span is not None:
                    new = _CMP_TEXT[_CMP_SWAPS[type(op)]]
                    mutations.append(Mutation(
                        span[0], span[1], span[2], new,
                        f"line {span[0]} col {span[1]}: `{token}` -> `{new}`",
                    ))
            case ast.BinOp(left=left, op=op, right=right) \
                    if type(op) in _ARITH_SWAPS:
                token = "+" if isinstance(op, ast.Add) else "-"
                span = _op_span(node, left, right, source_lines, token)
                if span is not None:
                    new = _ARITH_SWAPS[type(op)]
                    mutations.append(Mutation(
                        span[0], span[1], span[2], new,
                        f"line {span[0]} col {span[1]}: `{token}` -> `{new}`",
                    ))
            case ast.Constant(value=int() as v) if not isinstance(v, bool) \
                    and node.lineno == node.end_lineno and -100 <= v <= 100:
                mutations.append(Mutation(
                    node.lineno, node.col_offset, node.end_col_offset,
                    str(v + 1),
                    f"line {node.lineno} col {node.col_offset}: `{v}` -> `{v + 1}`",
                ))
            case ast.Call(func=ast.Name(id=("min" | "max") as fname) as func) \
                    if func.lineno == func.end_lineno:
                other = "max" if fname == "min" else "min"
                mutations.append(Mutation(
                    func.lineno, func.col_offset, func.end_col_offset, other,
                    f"line {func.lineno} col {func.col_offset}: `{fname}` -> `{other}`",
                ))
            case ast.BoolOp(op=op, values=[first, second, *_]) :
                token = "and" if isinstance(op, ast.And) else "or"
                span = _op_span(node, first, second, source_lines, token)
                if span is not None:
                    new = "or" if token == "and" else "and"
                    mutations.append(Mutation(
                        span[0], span[1], span[2], new,
                        f"line {span[0]} col {span[1]}: `{token}` -> `{new}`",
                    ))
            case _:
                pass

    mutations.extend(_operand_mutations(tree))
    # Select across families FIRST, then splice: capping by position alone
    # would let the cheapest family crowd the panel.
    mutations = _select(mutations, max_mutants)
    results: list[tuple[str, str]] = []
    seen: set[str] = set()
    for m in mutations:
        # Never mutate spec comments or docstrings: comments are invisible to
        # the AST, and int constants inside strings don't parse as Constants.
        mutated = _splice(source_lines, m)
        if mutated == source or mutated in seen:
            continue
        try:
            ast.parse(mutated)
        except SyntaxError:
            continue
        seen.add(mutated)
        results.append((m.description, mutated))
    return results
