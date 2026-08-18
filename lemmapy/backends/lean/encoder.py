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
`not/or`, quantifiers are `all()`/`any()` over explicit range domains),
so one `ast`-driven translator serves both spec clauses and body
expressions. Slice 2 adds predicate functions (`-> bool`, bridged into
Bool via `decide`, with `result == X` in ensures becoming an ↔ against
X-as-Prop) and single-binder bounded quantifiers (`forall`/`exists` over
`range` -> ∀/∃ with explicit bounds). ∃ goals need witnesses no fixed
tactic script can supply — those fail honestly as `postcondition` and
wait for the sidecar channel (P3).
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

# Every user-derived identifier (function, parameter, local, generated
# theorem) is emitted in Lean's escaped-identifier syntax «name». A
# keyword BLOCKLIST is inherently incomplete — `forall` escaped the
# first draft's list, and any keyword a future Lean adds would escape it
# forever — whereas «...» makes the KEYWORD collision class
# unrepresentable. Escaping does NOT separate user names from prelude
# names («PyAbs» IS the identifier PyAbs — guillemets quote, they do not
# namespace; measured as "`PyAbs` has already been declared"): that
# separation comes from the prelude's own namespace, referenced
# qualified (LemmaPy.PyAbs), which no top-level user def can redeclare
# and no binder can capture. The only collisions left are between
# emitted declarations themselves (`def f` beside `def f_spec`), which
# the reservation check below still refuses at the source line.


def _ident(name: str) -> str:
    return f"«{name}»"


def _check_name(name: str, what: str, line: int | None,
                taken: set[str]) -> None:
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
              result: str | None = None,
              rename: dict[str, str] | None = None) -> str:
    """An integer-valued Lean term. `result` is the application expression
    substituted for the reserved name `result` in ensures clauses;
    `rename` alpha-renames binders in theorem context (a parameter named
    after its own function would otherwise be captured by the function
    reference in the theorem statement)."""
    if isinstance(e, ast.Name):
        if e.id == "result":
            if result is None:
                raise _reject("`result` is only meaningful in `ensures`",
                              line)
            return result
        if e.id not in names:
            raise _reject(f"unknown name {e.id!r} in this slice "
                          f"(parameters and prior assignments only)", line)
        if rename and e.id in rename:
            return _ident(rename[e.id])
        return _ident(e.id)
    if isinstance(e, ast.Constant) and isinstance(e.value, int) \
            and not isinstance(e.value, bool):
        return str(e.value) if e.value >= 0 else f"({e.value})"
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.USub):
        return f"(-{_int_expr(e.operand, names, line, result, rename)})"
    if isinstance(e, ast.BinOp) and type(e.op) in _ARITH:
        a = _int_expr(e.left, names, line, result, rename)
        b = _int_expr(e.right, names, line, result, rename)
        return f"({a} {_ARITH[type(e.op)]} {b})"
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name):
        args = e.args
        if e.func.id in names:
            # The name is a parameter or local here: Python calls THAT
            # binding, not the builtin. Translating to the builtin would
            # let Lean verify mathematical abs/min/max while Python
            # invokes an integer — a certified different program (the
            # builtin-shadow class the Dafny encoder also refuses).
            raise _reject(f"call to {e.func.id!r}, which is shadowed by a "
                          f"parameter or local binding here — builtin "
                          f"shadowing is outside the fragment", line)
        if e.keywords:
            raise _reject(f"keyword arguments to {e.func.id!r} are not in "
                          f"the fragment", line)
        if e.func.id in ("min", "max") and len(args) == 2:
            a = _int_expr(args[0], names, line, result, rename)
            b = _int_expr(args[1], names, line, result, rename)
            return f"({e.func.id} {a} {b})"
        if e.func.id == "abs" and len(args) == 1:
            # Qualified: immune to user redeclaration AND binder capture
            # (a parameter named PyAbs shadows the bare name, never the
            # namespaced one).
            return (f"(LemmaPy.PyAbs "
                    f"{_int_expr(args[0], names, line, result, rename)})")
        if e.func.id == "old" and len(args) == 1 \
                and isinstance(args[0], ast.Name):
            # Parameters are immutable in this slice (reassignment is
            # rejected), so entry value == current value.
            return _int_expr(args[0], names, line, result, rename)
        raise _reject(f"call to {e.func.id!r} is outside slice 1 "
                      f"(min/max/abs/old only)", line)
    raise _reject(f"expression {ast.dump(e)[:60]}... is outside slice 1",
                  line)


def _quantifier(e: ast.Call, names: set[str], line: int,
                result: str | None, rename: dict[str, str] | None,
                result_is_bool: bool,
                avoid: frozenset[str] | None = None) -> str | None:
    """`all((body) for v in (range(a, b)))` -> a bounded ∀ (any -> ∃).

    The desugared form the frontend emits for `forall`/`exists` spec
    clauses. Only a single binder over `range` is in slice 2; anything
    else falls through to the caller's rejection."""
    if not (isinstance(e.func, ast.Name) and e.func.id in ("all", "any")
            and e.func.id not in names
            and len(e.args) == 1 and not e.keywords
            and isinstance(e.args[0], ast.GeneratorExp)):
        return None
    gen = e.args[0]
    if len(gen.generators) != 1:
        raise _reject("only one quantifier binder per clause in slice 2",
                      line)
    comp = gen.generators[0]
    if comp.ifs or comp.is_async or not isinstance(comp.target, ast.Name):
        raise _reject("filtered or destructuring quantifier binders are "
                      "outside slice 2", line)
    it = comp.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
            and it.func.id == "range" and it.func.id not in names
            and not it.keywords and len(it.args) in (1, 2)):
        raise _reject("quantifier domains must be `range(a, b)` or "
                      "`range(b)` in slice 2 (and `range` must not be "
                      "shadowed)", line)
    if len(it.args) == 2:
        lo = _int_expr(it.args[0], names, line, result, rename)
        hi = _int_expr(it.args[1], names, line, result, rename)
    else:
        lo = "0"
        hi = _int_expr(it.args[0], names, line, result, rename)
    v = comp.target.id
    # Two capture hazards at the binder, both measured classes:
    # 1. The theorem's rename map (param named after its own function)
    #    must NOT apply under a binder that reuses the renamed name —
    #    the body would reference the OUTER parameter and Lean would
    #    verify a different contract than the source spec.
    # 2. The body may contain `result`, whose translation embeds the
    #    function and parameter names — a binder sharing any of those
    #    names would capture them. `avoid` carries that set from theorem
    #    emission; the binder is alpha-renamed off it (fresh primes),
    #    sound because comprehension binder names are arbitrary.
    body_rename = {k: r for k, r in (rename or {}).items() if k != v}
    binder = v
    if avoid:
        while binder in avoid:
            binder += "'"
    if binder != v:
        body_rename[v] = binder
    # The body's avoid set grows by THIS binder's emitted name: a
    # nested quantifier reusing an alpha-renamed name would otherwise
    # land on the outer binder's emitted name and capture it (the same
    # transitive-capture class as the theorem-rename hole, one scope
    # deeper).
    body_avoid = (avoid or frozenset()) | {binder}
    body = _prop_expr(gen.elt, names | {v}, line, result,
                      body_rename or None, result_is_bool, body_avoid)
    bound = f"({lo} ≤ {_ident(binder)} ∧ {_ident(binder)} < {hi})"
    if e.func.id == "all":
        return f"(∀ {_ident(binder)} : Int, {bound} → {body})"
    return f"(∃ {_ident(binder)} : Int, {bound} ∧ {body})"


def _prop_expr(e: ast.expr, names: set[str], line: int,
               result: str | None = None,
               rename: dict[str, str] | None = None,
               result_is_bool: bool = False,
               avoid: frozenset[str] | None = None) -> str:
    """A proposition-valued Lean term (spec clauses, `if` conditions).

    With `result_is_bool`, the reserved name `result` denotes a Bool
    application: bare `result` becomes the proposition `app = true`, and
    `result == X` / `result != X` become ↔ / ¬↔ against X-as-Prop — the
    Bool/Prop bridge for predicate functions."""
    if result_is_bool and isinstance(e, ast.Name) and e.id == "result":
        if result is None:
            raise _reject("`result` is only meaningful in `ensures`", line)
        return f"({result} = true)"
    if result_is_bool and isinstance(e, ast.Compare) \
            and len(e.ops) == 1 and type(e.ops[0]) in (ast.Eq, ast.NotEq):
        sides = (e.left, e.comparators[0])
        others = [s for s in sides
                  if not (isinstance(s, ast.Name) and s.id == "result")]
        if len(others) == 1:
            if result is None:
                raise _reject("`result` is only meaningful in `ensures`",
                              line)
            prop = _prop_expr(others[0], names, line, result, rename,
                              result_is_bool, avoid)
            iff = f"(({result} = true) ↔ {prop})"
            return iff if isinstance(e.ops[0], ast.Eq) else f"(¬{iff})"
    if isinstance(e, ast.Call):
        q = _quantifier(e, names, line, result, rename, result_is_bool,
                        avoid)
        if q is not None:
            return q
    if isinstance(e, ast.Compare):
        parts = []
        left = e.left
        for op, right in zip(e.ops, e.comparators):
            if type(op) not in _CMP:
                raise _reject("only =/≠/</≤/>/≥ comparisons are in slice 1",
                              line)
            a = _int_expr(left, names, line, result, rename)
            b = _int_expr(right, names, line, result, rename)
            parts.append(f"{a} {_CMP[type(op)]} {b}")
            left = right
        return "(" + " ∧ ".join(parts) + ")"
    if isinstance(e, ast.BoolOp):
        op = "∧" if isinstance(e.op, ast.And) else "∨"
        parts = [_prop_expr(v, names, line, result, rename,
                            result_is_bool, avoid)
                 for v in e.values]
        return "(" + f" {op} ".join(parts) + ")"
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
        inner = _prop_expr(e.operand, names, line, result, rename,
                           result_is_bool, avoid)
        return f"(¬{inner})"
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


def _bool_expr(e: ast.expr, names: set[str], line: int) -> str:
    """A Bool-valued Lean term for a predicate function's return.

    `decide` bridges the translated Prop into Bool; True/False literals
    map directly. Anything else (a bool-typed local, a bool call) is
    outside slice 2."""
    if isinstance(e, ast.Constant) and e.value is True:
        return "true"
    if isinstance(e, ast.Constant) and e.value is False:
        return "false"
    if isinstance(e, (ast.Compare, ast.BoolOp, ast.UnaryOp)):
        return f"(decide {_prop_expr(e, names, line)})"
    raise _reject("a bool return must be True/False or a boolean "
                  "expression in slice 2", line)


def _body_expr(stmts: list[ast.stmt], names: set[str],
               params: tuple[str, ...], is_bool: bool = False) -> str:
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
        if is_bool:
            return _bool_expr(head.value, names, head.lineno)
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
        value = _int_expr(head.value, names, head.lineno)
        return (f"let {_ident(target)} := {value}; "
                + _body_expr(rest, names | {target}, params, is_bool))
    if isinstance(head, ast.If):
        cond = _prop_expr(head.test, names, head.lineno)
        then = _body_expr(head.body, names, params, is_bool)
        if head.orelse:
            if rest:
                raise _reject("unreachable code after an if/else in which "
                              "both branches return", rest[0].lineno)
            other = _body_expr(head.orelse, names, params, is_bool)
        else:
            if not _always_returns(head.body):
                raise _reject("an `if` without `else` must return in its "
                              "body (slice 1 compiles it to a conditional "
                              "expression)", head.lineno)
            other = _body_expr(rest, names, params, is_bool)
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
    # Module level admits ONLY function definitions and a docstring.
    # Anything else — an assignment (`abs = ...`), an import binding
    # (`import numpy as abs`), a class — could rebind a name call sites
    # translate as a builtin, and enumerating the dangerous forms would
    # rebuild the blocklist mistake: rejection of the whole statement
    # class makes the module-binding shadow unrepresentable.
    for i, stmt in enumerate(module.body):
        if isinstance(stmt, ast.FunctionDef):
            continue
        if i == 0 and isinstance(stmt, ast.Expr) \
                and isinstance(stmt.value, ast.Constant) \
                and isinstance(stmt.value.value, str):
            continue  # module docstring
        raise _reject(
            f"module-level `{type(stmt).__name__}` is outside the lean "
            f"slice (function definitions and a docstring only — a "
            f"module binding could shadow a builtin the encoder "
            f"translates)", stmt.lineno)
    # Duplicate defs mispair contract and body: specs attach to the
    # FIRST definition, the name map would keep the LAST (and CPython
    # runs the last), so the encoder would prove a body against another
    # definition's contract. Same refusal as the Dafny encoder's.
    seen_defs: dict[str, int] = {}
    for n in module.body:
        if isinstance(n, ast.FunctionDef):
            if n.name in seen_defs:
                raise _reject(
                    f"duplicate definition of {n.name!r} (first at line "
                    f"{seen_defs[n.name]}) — CPython runs the last def; "
                    f"the verifier would pair the first def's contract "
                    f"with the last def's body", n.lineno)
            seen_defs[n.name] = n.lineno
    by_name = {n.name: n for n in module.body
               if isinstance(n, ast.FunctionDef)}
    # Builtin-shadow check, the Dafny encoder's discipline applied here:
    # a module-level def named after an encoder builtin would vanish from
    # the model while call sites translate to the builtin — Lean would
    # verify mathematical abs/min/max while Python calls the user's def.
    for shadow in by_name:
        if shadow in ("abs", "min", "max", "old", "all", "any", "range",
                      "result"):
            raise _reject(
                f"module-level def {shadow!r} shadows an encoder builtin "
                f"— call sites would verify the builtin while Python "
                f"calls this def", by_name[shadow].lineno)

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
        if fn.lineno != spec_fn.lineno:
            # Name-only pairing would let a spec attached to a NESTED
            # def borrow a module-level body sharing the name — Lean
            # would certify a different function than the annotated one.
            # The def line is part of the pairing key, same as the Dafny
            # encoder's (name, lineno) index.
            raise _reject(
                f"spec for {spec_fn.name!r} is attached to a definition "
                f"at line {spec_fn.lineno}, not the module-level def at "
                f"line {fn.lineno} — nested functions are outside the "
                f"lean slice", spec_fn.lineno)
        if fn.decorator_list:
            # A decorator can replace or wrap the callable, so proving
            # fn.body would certify a contract for a function Python
            # never runs (the survey's X-DECOR exclusion, enforced here).
            raise _reject(
                f"decorated functions are outside the lean slice — the "
                f"decorator may replace the callable, so the modeled "
                f"body is not what Python executes",
                fn.decorator_list[0].lineno)
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
            # No module-wide check for parameters: a binder shadowing a
            # top-level name is legal Lean (and matches Python scoping).
            # The one genuine capture — a parameter named after its OWN
            # function, which the theorem statement must reference beside
            # it — is alpha-renamed in theorem context below.
        ret = fn.returns
        if not (isinstance(ret, ast.Name) and ret.id in ("int", "bool")):
            raise _reject("return type must be `int` or `bool` in this "
                          "slice", fn.lineno)
        is_bool = ret.id == "bool"
        params = tuple(arg.arg for arg in a.args)
        names = set(params)

        # Python scoping: a name ASSIGNED anywhere in the function is
        # local for the whole function, so a call BEFORE the assignment
        # raises UnboundLocalError at runtime. The sequential shadow
        # check in _int_expr only sees prior assignments; this pre-scan
        # closes the call-before-assign half (Lean would otherwise
        # verify the mathematical builtin on a path Python never
        # executes).
        assigned_anywhere = {
            tgt.id for node in ast.walk(fn) if isinstance(node, ast.Assign)
            for tgt in node.targets if isinstance(tgt, ast.Name)}
        for node in ast.walk(fn):
            if isinstance(node, ast.Call) \
                    and isinstance(node.func, ast.Name) \
                    and node.func.id in assigned_anywhere:
                raise _reject(
                    f"call to {node.func.id!r}, which is assigned later "
                    f"in this function — Python treats it as local "
                    f"throughout (UnboundLocalError here), so the call "
                    f"cannot mean the builtin", node.lineno)

        binders = " ".join(f"({_ident(p)} : Int)" for p in params)
        body = _body_expr([s for s in fn.body
                           if not (isinstance(s, ast.Expr)
                                   and isinstance(s.value, ast.Constant))],
                          names, params, is_bool)
        ret_ty = "Bool" if is_bool else "Int"
        emit("", None)
        emit(f"def {_ident(spec_fn.name)} {binders} : {ret_ty} :=",
             fn.lineno)
        emit(f"  {body}", fn.lineno)

        ensures = _parse_clause(spec_fn, "ensures")
        if not ensures:
            continue
        # Theorem context: the statement references the function AND its
        # parameters by name, so a parameter named after its own function
        # would capture the function reference. Binder names in a theorem
        # are arbitrary — alpha-rename that one parameter (p -> p').
        rename = ({spec_fn.name: spec_fn.name + "'"}
                  if spec_fn.name in params else None)

        def _tname(p: str) -> str:
            return rename[p] if rename and p in rename else p

        thm_binders = " ".join(f"({_ident(_tname(p))} : Int)"
                               for p in params)
        app = ("(" + " ".join([_ident(spec_fn.name),
                               *(_ident(_tname(p)) for p in params)]) + ")")
        # The binder-avoid set must cover the RENAMED theorem binders
        # too: with rename {f: f'}, a quantifier binder f fresh-renames
        # to f' — precisely the renamed parameter, capture one level up
        # (measured: the binder==fn==param case proved the WRONG goal,
        # ∀ f', f(f') ≥ f'+5, and failed a true spec).
        avoid = (frozenset(params) | {spec_fn.name}
                 | frozenset((rename or {}).values()))
        hyps = []
        for i, (expr, line) in enumerate(_parse_clause(spec_fn, "requires")):
            hyps.append(
                f"(h{i} : "
                f"{_prop_expr(expr, names, line, rename=rename, avoid=avoid)})")
        posts = [(_prop_expr(expr, names, line, result=app,
                             rename=rename, result_is_bool=is_bool,
                             avoid=avoid), line)
                 for expr, line in ensures]
        goal = " ∧ ".join(p for p, _ in posts)
        sig = " ".join(x for x in [thm_binders, *hyps] if x)
        first_ensures_line = posts[0][1]
        theorem = f"{spec_fn.name}_spec"
        theorems.append(theorem)
        emit("", None)
        emit(f"theorem {_ident(theorem)} {sig} :", first_ensures_line)
        emit(f"    {goal} := by", first_ensures_line)
        # The failing-goal diagnostic lands on the tactic lines; map them
        # to the first ensures clause so a `postcondition` failure points
        # at the contract, not at Lean plumbing.
        emit(f"  unfold {_ident(spec_fn.name)}", first_ensures_line)
        # Prelude definitions are opaque to omega — a goal containing
        # LemmaPy.PyAbs is unprovable until it unfolds to its
        # if-then-else (measured: every abs()-using module failed as
        # postcondition, shadowed or not — no earlier live case called
        # abs). `try`, because unfold fails when the constant does not
        # occur.
        emit("  try unfold LemmaPy.PyAbs", first_ensures_line)
        # `dsimp only` zeta-reduces the `let`s the body compiler emits
        # for Python locals — omega does not look through let-bindings
        # (measured: a one-local module failed with the local itself in
        # omega's counterexample; bump/clamp never caught it because
        # they bind no locals). `try`, because dsimp FAILS outright on
        # "no progress" (measured: it regressed let-free clamp to a
        # failed unknown before the try).
        emit("  try dsimp only", first_ensures_line)
        # Predicate functions bridge Bool to Prop via `decide`; the
        # simp lemma turns `decide p = true` goals back into `p` so
        # omega sees arithmetic, not booleans.
        emit("  try simp only [decide_eq_true_eq]", first_ensures_line)
        emit("  repeat' split", first_ensures_line)
        # Bounded-quantifier goals open with ∀/→; intros peels them so
        # omega faces the linear body (∃ goals need witnesses no fixed
        # script can supply — those fail honestly as postcondition and
        # wait for the sidecar channel).
        emit("  all_goals (try intros)", first_ensures_line)
        # simp_all normalizes the residue the earlier steps leave:
        # Bool-literal ite under an iff ((if P then true else false) =
        # true ↔ P) and trivial-side iffs hiding vacuous quantifiers —
        # both measured in the slice-2 matrix. Goals it fully closes are
        # done; whatever remains must be linear arithmetic for omega,
        # with `trivial` as the last resort for reflexive leftovers.
        emit("  all_goals (try simp_all)", first_ensures_line)
        emit("  all_goals (first | omega | trivial)", first_ensures_line)

    return LeanEncoded(lean_source="\n".join(lines) + "\n",
                       line_map=line_map, theorems=theorems)
