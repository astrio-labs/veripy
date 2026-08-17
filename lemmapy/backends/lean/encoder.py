"""Python fragment -> Lean 4, slice 1: loop-free integer functions.

Shallow functional embedding (ROADMAP, Lean track P1): each fragment
function becomes a Lean `def`, and its `#@ requires`/`#@ ensures`
contract becomes one theorem

    theorem f_spec (params) (h0 : Pre0) ... : Post0 ∧ Post1 := by
      unfold f
      repeat' split
      all_goals omega

`repeat' split` peels the `if … then … else` terms the body compiler
emits for Python conditionals; `omega` discharges the linear
integer-arithmetic goals this slice's fragment can express. Where the
cocktail fails, the theorem fails — that is a prover verdict, not an
encoding error, and it surfaces through the driver as a `postcondition`
failure mapped to the ensures clause.

Everything outside the slice is REJECTED loudly with the shared
`EncodeError` (kind `conformance` in the payload): loops, non-`int`
params, parameter reassignment, `#@ proof` clauses (the sidecar channel
lands in P3), and operators this slice does not model (`//`, `%`, `**`
arrive with the P2 prelude growth). The Dafny fragment is the outer
bound; this slice is a strict subset of it, and a construct the Dafny
backend accepts but this one does not must fail loudly rather than
verify vacuously.

Spec expressions arrive DESUGARED from the frontend (`==>` is already
`not/or`, quantifiers are `all()`/`any()` — rejected here until slice 2),
so one `ast`-driven translator serves both spec clauses and body
expressions.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass

from ...frontend.parse import FunctionSpec, ModuleSpecs
# The shared encode-failure type (its neutral home arrives when the
# taxonomy next versions; the class carries message/line/rule already).
from ..dafny.encoder import EncodeError
from .prelude import PRELUDE, PRELUDE_VERSION  # noqa: F401  (version re-exported)

_SLICE_RULE = "lean-slice-1"

# Names the emitted artifact already owns. A Python `def PyAbs` (prelude
# collision), a `def f` next to a `def f_spec` (theorem collision), or a
# parameter named `then` (keyword collision) would emit duplicate or
# unparseable Lean declarations — Lean's complaint would then surface as
# a confusing prover error on valid-looking Python, so the encoder
# rejects the collision at the source line instead (the same class the
# Dafny encoder's builtin-shadow check closes).
_PRELUDE_NAMES = frozenset({"PyAbs"})
_LEAN_KEYWORDS = frozenset({
    "def", "theorem", "lemma", "let", "if", "then", "else", "by", "fun",
    "match", "with", "do", "return", "have", "show", "from", "in",
    "min", "max", "abs", "True", "False", "Int", "Nat", "Prop", "Type",
    "sorry", "axiom", "instance", "structure", "inductive", "where",
})


def _check_name(name: str, what: str, line: int | None,
                taken: set[str]) -> None:
    if name in _PRELUDE_NAMES:
        raise _reject(f"{what} {name!r} collides with a prelude "
                      f"declaration", line)
    if name in _LEAN_KEYWORDS:
        raise _reject(f"{what} {name!r} collides with a Lean keyword or "
                      f"builtin", line)
    if name in taken:
        raise _reject(f"{what} {name!r} collides with another emitted "
                      f"declaration", line)


@dataclass
class LeanEncoded:
    lean_source: str
    line_map: dict[int, int]  # 1-based lean line -> python line
    theorems: list[str]


def _reject(message: str, line: int | None) -> EncodeError:
    return EncodeError(message, line, rule=_SLICE_RULE)


# --- expression translation -------------------------------------------------

_CMP = {ast.Eq: "=", ast.NotEq: "≠", ast.Lt: "<", ast.LtE: "≤",
        ast.Gt: ">", ast.GtE: "≥"}
_ARITH = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}


def _int_expr(e: ast.expr, names: set[str], line: int,
              result: str | None = None) -> str:
    """An integer-valued Lean term. `result` is the application expression
    substituted for the reserved name `result` in ensures clauses."""
    if isinstance(e, ast.Name):
        if e.id == "result":
            if result is None:
                raise _reject("`result` is only meaningful in `ensures`",
                              line)
            return result
        if e.id not in names:
            raise _reject(f"unknown name {e.id!r} in this slice "
                          f"(parameters and prior assignments only)", line)
        return e.id
    if isinstance(e, ast.Constant) and isinstance(e.value, int) \
            and not isinstance(e.value, bool):
        return str(e.value) if e.value >= 0 else f"({e.value})"
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.USub):
        return f"(-{_int_expr(e.operand, names, line, result)})"
    if isinstance(e, ast.BinOp) and type(e.op) in _ARITH:
        a = _int_expr(e.left, names, line, result)
        b = _int_expr(e.right, names, line, result)
        return f"({a} {_ARITH[type(e.op)]} {b})"
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name):
        args = e.args
        if e.keywords:
            raise _reject(f"keyword arguments to {e.func.id!r} are not in "
                          f"the fragment", line)
        if e.func.id in ("min", "max") and len(args) == 2:
            a = _int_expr(args[0], names, line, result)
            b = _int_expr(args[1], names, line, result)
            return f"({e.func.id} {a} {b})"
        if e.func.id == "abs" and len(args) == 1:
            return f"(PyAbs {_int_expr(args[0], names, line, result)})"
        if e.func.id == "old" and len(args) == 1 \
                and isinstance(args[0], ast.Name):
            # Parameters are immutable in this slice (reassignment is
            # rejected), so entry value == current value.
            return _int_expr(args[0], names, line, result)
        raise _reject(f"call to {e.func.id!r} is outside slice 1 "
                      f"(min/max/abs/old only)", line)
    raise _reject(f"expression {ast.dump(e)[:60]}... is outside slice 1",
                  line)


def _prop_expr(e: ast.expr, names: set[str], line: int,
               result: str | None = None) -> str:
    """A proposition-valued Lean term (spec clauses, `if` conditions)."""
    if isinstance(e, ast.Compare):
        parts = []
        left = e.left
        for op, right in zip(e.ops, e.comparators):
            if type(op) not in _CMP:
                raise _reject("only =/≠/</≤/>/≥ comparisons are in slice 1",
                              line)
            a = _int_expr(left, names, line, result)
            b = _int_expr(right, names, line, result)
            parts.append(f"{a} {_CMP[type(op)]} {b}")
            left = right
        return "(" + " ∧ ".join(parts) + ")"
    if isinstance(e, ast.BoolOp):
        op = "∧" if isinstance(e.op, ast.And) else "∨"
        parts = [_prop_expr(v, names, line, result) for v in e.values]
        return "(" + f" {op} ".join(parts) + ")"
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
        return f"(¬{_prop_expr(e.operand, names, line, result)})"
    if isinstance(e, ast.Constant) and e.value is True:
        return "True"
    if isinstance(e, ast.Constant) and e.value is False:
        return "False"
    raise _reject("spec expression outside slice 1 (comparisons and "
                  "and/or/not over integers; quantifiers arrive in "
                  "slice 2)", line)


# --- body compilation -------------------------------------------------------

def _always_returns(stmts: list[ast.stmt]) -> bool:
    for s in stmts:
        if isinstance(s, ast.Return):
            return True
        if isinstance(s, ast.If) and s.orelse \
                and _always_returns(s.body) and _always_returns(s.orelse):
            return True
    return False


def _body_expr(stmts: list[ast.stmt], names: set[str],
               params: tuple[str, ...]) -> str:
    """Compile a loop-free statement list to one Lean term."""
    if not stmts:
        raise _reject("fall through the end of the function without a "
                      "return", None)
    head, rest = stmts[0], stmts[1:]
    if isinstance(head, ast.Return):
        if head.value is None:
            raise _reject("bare `return` has no value to encode",
                          head.lineno)
        if rest:
            raise _reject("unreachable code after `return`",
                          rest[0].lineno)
        return _int_expr(head.value, names, head.lineno)
    if isinstance(head, ast.Assign):
        if len(head.targets) != 1 \
                or not isinstance(head.targets[0], ast.Name):
            raise _reject("only single-name assignment is in slice 1",
                          head.lineno)
        target = head.targets[0].id
        if target in params:
            raise _reject(f"reassigning parameter {target!r} is outside "
                          f"slice 1 (parameters are immutable so that "
                          f"`old()` needs no snapshots)", head.lineno)
        # A local named `then` (or `PyAbs`) would emit an unparseable or
        # shadowing `let`; Lean's complaint would masquerade as a prover
        # error on valid-looking Python.
        _check_name(target, "local", head.lineno, set())
        value = _int_expr(head.value, names, head.lineno)
        return (f"let {target} := {value}; "
                + _body_expr(rest, names | {target}, params))
    if isinstance(head, ast.If):
        cond = _prop_expr(head.test, names, head.lineno)
        then = _body_expr(head.body, names, params)
        if head.orelse:
            if rest:
                raise _reject("unreachable code after an if/else in which "
                              "both branches return", rest[0].lineno)
            other = _body_expr(head.orelse, names, params)
        else:
            if not _always_returns(head.body):
                raise _reject("an `if` without `else` must return in its "
                              "body (slice 1 compiles it to a conditional "
                              "expression)", head.lineno)
            other = _body_expr(rest, names, params)
        return f"(if {cond} then {then} else {other})"
    raise _reject(f"`{type(head).__name__}` is outside the lean backend's "
                  f"slice-1 fragment (loop-free integer functions; loops "
                  f"arrive in P2)", head.lineno)


# --- module emission --------------------------------------------------------

def _parse_clause(spec_fn: FunctionSpec, kind: str) -> list[tuple[ast.expr, int]]:
    out = []
    for c in spec_fn.by_kind(kind):
        text = c.desugared if c.desugared is not None else c.raw
        try:
            tree = ast.parse(text, mode="eval")
        except SyntaxError as exc:
            raise _reject(f"cannot parse {kind} clause: {exc.msg}", c.line)
        out.append((tree.body, c.line))
    return out


def encode_module_lean(source: str, specs: ModuleSpecs, module_name: str,
                       proof_lemmas: frozenset[str] = frozenset()
                       ) -> LeanEncoded:
    if specs.errors:
        first = specs.errors[0]
        raise EncodeError(f"spec error: {first.error}", first.line)
    if proof_lemmas:
        raise _reject("proof sidecars land in the Lean track's P3; this "
                      "slice proves with its fixed tactic script only",
                      None)
    module = ast.parse(source)
    by_name = {n.name: n for n in module.body
               if isinstance(n, ast.FunctionDef)}

    lines: list[str] = PRELUDE.split("\n")
    line_map: dict[int, int] = {}
    theorems: list[str] = []

    def emit(text: str, py_line: int | None) -> None:
        for part in text.split("\n"):
            lines.append(part)
            if py_line is not None:
                line_map[len(lines)] = py_line

    # Reserve every emitted top-level name up front, so `def f` next to
    # `def f_spec` collides regardless of definition order.
    taken: set[str] = set()
    for spec_fn in specs.functions:
        fn = by_name.get(spec_fn.name)
        line = fn.lineno if fn is not None else spec_fn.lineno
        _check_name(spec_fn.name, "function", line, taken)
        taken.add(spec_fn.name)
        if spec_fn.by_kind("ensures"):
            _check_name(f"{spec_fn.name}_spec", "generated theorem for",
                        line, taken)
            taken.add(f"{spec_fn.name}_spec")

    for spec_fn in specs.functions:
        if spec_fn.by_kind("proof"):
            raise _reject("`#@ proof` clauses need the sidecar channel "
                          "(Lean track P3)", spec_fn.by_kind("proof")[0].line)
        fn = by_name.get(spec_fn.name)
        if fn is None:
            raise _reject(f"spec for unknown function {spec_fn.name!r}",
                          spec_fn.lineno)
        a = fn.args
        # Anything beyond plain positional parameters would be silently
        # erased from the binder list — a wrong-arity artifact, or
        # phantom "unknown name" rejections for parameters that exist.
        if a.posonlyargs or a.kwonlyargs or a.vararg or a.kwarg \
                or a.defaults or a.kw_defaults:
            raise _reject("only plain positional parameters (no defaults, "
                          "no *args/**kwargs, no positional-only or "
                          "keyword-only markers) are in slice 1", fn.lineno)
        for arg in a.args:
            ann = arg.annotation
            if not (isinstance(ann, ast.Name) and ann.id == "int"):
                raise _reject(f"parameter {arg.arg!r} must be `int` in "
                              f"slice 1", fn.lineno)
            _check_name(arg.arg, "parameter", fn.lineno, taken)
        ret = fn.returns
        if not (isinstance(ret, ast.Name) and ret.id == "int"):
            raise _reject("return type must be `int` in slice 1", fn.lineno)
        params = tuple(arg.arg for arg in a.args)
        names = set(params)

        binders = " ".join(f"({p} : Int)" for p in params)
        body = _body_expr([s for s in fn.body
                           if not (isinstance(s, ast.Expr)
                                   and isinstance(s.value, ast.Constant))],
                          names, params)
        emit("", None)
        emit(f"def {spec_fn.name} {binders} : Int :=", fn.lineno)
        emit(f"  {body}", fn.lineno)

        ensures = _parse_clause(spec_fn, "ensures")
        if not ensures:
            continue
        app = "(" + " ".join([spec_fn.name, *params]) + ")"
        hyps = []
        for i, (expr, line) in enumerate(_parse_clause(spec_fn, "requires")):
            hyps.append(f"(h{i} : {_prop_expr(expr, names, line)})")
        posts = [(_prop_expr(expr, names, line, result=app), line)
                 for expr, line in ensures]
        goal = " ∧ ".join(p for p, _ in posts)
        sig = " ".join(x for x in [binders, *hyps] if x)
        first_ensures_line = posts[0][1]
        theorem = f"{spec_fn.name}_spec"
        theorems.append(theorem)
        emit("", None)
        emit(f"theorem {theorem} {sig} :", first_ensures_line)
        emit(f"    {goal} := by", first_ensures_line)
        # The failing-goal diagnostic lands on the tactic lines; map them
        # to the first ensures clause so a `postcondition` failure points
        # at the contract, not at Lean plumbing.
        emit(f"  unfold {spec_fn.name}", first_ensures_line)
        emit("  repeat' split", first_ensures_line)
        emit("  all_goals omega", first_ensures_line)

    return LeanEncoded(lean_source="\n".join(lines) + "\n",
                       line_map=line_map, theorems=theorems)
