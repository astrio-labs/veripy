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
lands in P3), and operators this slice does not model (`**` arrives with
further P2 prelude growth). The Dafny fragment is the outer
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

The P2 slices grow the fragment, same discipline: for-range accumulator
loops compile to fuel recursion with the `#@ invariant` as a generated
induction theorem, and `list[int]` parameters arrive with `len`/`sum`
(the prelude's PySum, with a PROVED prefix-sum lemma pack), indexing
where in-bounds is guaranteed by construction (`_ListCtx`), and
`sum(xs[:i])` prefix sums in invariants.

`//` and `%` model Python EXACTLY (floor division, divisor-signed
remainder — `Int.fdiv`/`Int.fmod`, never Lean's own `/` and `%`, which
are ediv/emod and agree only for positive divisors). Because Python
RAISES on a zero divisor while the Lean models are total, every divisor
carries a well-formedness obligation discharged from the contract, and
the generated proof supplies the bounds omega cannot derive for a
variable divisor.
"""

from __future__ import annotations

import ast
import copy
from dataclasses import dataclass

from ...frontend.parse import FunctionSpec, ModuleSpecs
# The shared encode-failure type (its neutral home arrives when the
# taxonomy next versions; the class carries message/line/rule already).
from ..dafny.encoder import EncodeError
from .prelude import PRELUDE, PRELUDE_VERSION  # noqa: F401  (version re-exported)

_SLICE_RULE = "lean-slice-1"

_MATH_FNS = frozenset({"gcd", "factorial", "isqrt"})
_MATH_LEAN = (
    "math.gcd/factorial/isqrt are outside the Lean slice — the Dafny "
    "backend admits them as PyGcd/PyFact/PyIsqrt; this slice has no "
    "math prelude"
)
_DAFNY_STR_METHODS = frozenset({
    "join", "split", "find", "startswith", "endswith", "replace",
    "strip", "lstrip", "rstrip",
})

# Every user-derived identifier (function, parameter, local, generated
# theorem) is emitted in Lean's escaped-identifier syntax «name». A
# keyword BLOCKLIST is inherently incomplete — `forall` escaped the
# first draft's list, and any keyword a future Lean adds would escape it
# forever — whereas «...» makes the KEYWORD collision class
# unrepresentable. Escaping does NOT separate user names from prelude
# names («PyAbs» IS the identifier PyAbs — guillemets quote, they do not
# namespace; measured as "`PyAbs` has already been declared"): that
# separation comes from the prelude's own namespace, referenced
# qualified (VeriPy.PyAbs), which no top-level user def can redeclare
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


def _lref(name: str, rename: dict[str, str] | None) -> str:
    return _ident(rename[name]) if rename and name in rename else _ident(name)


@dataclass
class _ListCtx:
    """Which names are `list[int]` parameters, and which index names are
    STRUCTURALLY in bounds for which list.

    `xs[i]` is total in Lean (`getD` with default 0) but partial in
    Python (IndexError, and negative indices wrap), so the two agree
    only where 0 ≤ i < len(xs) is guaranteed by construction: the loop
    index of `for i in range(len(xs))`, or a quantifier binder over
    `range(len(xs))` whose bound hypothesis guards the body. `safe_idx`
    carries exactly those (index, list) pairs; every other index is
    refused. `take_idx` names the one variable allowed as `xs[:i]`'s
    upper bound — the loop index, and only while translating the
    invariant, where the slice is proof scaffolding evaluated at loop
    heads (i ≥ 0 there, so Lean's `.toNat` clamp is never observed)."""

    lists: frozenset[str]
    safe_idx: dict[str, str]
    take_idx: str | None
    # Scaffold mode (invariant clauses only): the translated Prop is
    # proof machinery, never executed and not part of the contract, so
    # `getD`'s totalization cannot break ensures fidelity. Quantifier
    # binders become safe indices into ANY list (recorded as "*"),
    # which is what prefix invariants like
    # `b == all(xs[k] < t for k in range(i))` need — k's domain is the
    # index prefix, not range(len(xs)).
    scaffold: bool = False
    # Contract-guarded literal indexing: `min_len[L] = b` records a
    # top-level `len(L) > c` / `len(L) >= c` requires conjunct (b the
    # implied lower bound), licensing literal indices below b — the
    # max_element pattern `m = l[0]` under `requires len(l) > 0`. The
    # certification is CONDITIONAL, exactly like Dafny's: inputs
    # violating the requires are outside the contract (Python raises,
    # the runtime gate rejects, the theorem assumes the hypothesis).
    min_len: dict[str, int] | None = None
    # Contract-derived positivity, the same kind of fact as `min_len`: names
    # a top-level `requires` conjunct proves are > 0. Python's `//` and `%`
    # RAISE on a zero divisor while Lean's fdiv/fmod return 0, so a divisor
    # that is not provably nonzero would let Lean certify a program CPython
    # cannot run. This slice discharges that obligation only via positivity,
    # which is also the domain where the prelude's omega bridges apply.
    pos_names: frozenset[str] = frozenset()
    # For a list-returning function: the parameter whose length an
    # EARLIER `ensures` proved equal to `result`'s. That is what makes
    # `result[i]` in bounds when `i` ranges over that list, and it rides
    # the same clause-ordering rule as divisor positivity.
    result_list: str | None = None
    # Does the function actually RETURN a list? Without this, a spec
    # writing `len(result)` on an int-returning function emitted
    # `.length` on an Int and Lean failed to elaborate — a tool error
    # where the encoder owed a refusal.
    result_is_list: bool = False
    # Names the contract proves >= 0. Weaker than `pos_names`, and
    # enough for an exponent, where zero is a perfectly good value.
    nonneg_names: frozenset[str] = frozenset()

    def positive(self, e: "ast.expr") -> bool:
        if isinstance(e, ast.Constant) and isinstance(e.value, int) \
                and not isinstance(e.value, bool):
            return e.value > 0
        return isinstance(e, ast.Name) and e.id in self.pos_names

    def safe(self, idx: str) -> str | None:
        return self.safe_idx.get(idx)

    def safe_for(self, idx: str, lst: str) -> bool:
        return self.safe_idx.get(idx) in (lst, "*")

    def literal_ok(self, c: int, lst: str) -> bool:
        return 0 <= c < (self.min_len or {}).get(lst, 0)


_NO_LISTS = _ListCtx(frozenset(), {}, None)


def _int_expr(e: ast.expr, names: set[str], line: int,
              result: str | None = None,
              rename: dict[str, str] | None = None,
              lc: _ListCtx | None = None) -> str:
    """An integer-valued Lean term. `result` is the application expression
    substituted for the reserved name `result` in ensures clauses;
    `rename` alpha-renames binders in theorem context (a parameter named
    after its own function would otherwise be captured by the function
    reference in the theorem statement); `lc` carries the list-typed
    names and the structurally-safe index pairs."""
    lc = lc or _NO_LISTS
    if isinstance(e, ast.Name):
        if e.id == "result":
            if result is None:
                raise _reject("`result` is only meaningful in `ensures`",
                              line)
            return result
        if e.id not in names:
            raise _reject(f"unknown name {e.id!r} in this slice "
                          f"(parameters and prior assignments only)", line)
        if e.id in lc.lists:
            raise _reject(f"list parameter {e.id!r} in an integer "
                          f"position (lists appear only under len/sum/"
                          f"indexing in this slice)", line)
        if rename and e.id in rename:
            return _ident(rename[e.id])
        return _ident(e.id)
    if isinstance(e, ast.Constant) and isinstance(e.value, int) \
            and not isinstance(e.value, bool):
        return str(e.value) if e.value >= 0 else f"({e.value})"
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.USub):
        return f"(-{_int_expr(e.operand, names, line, result, rename, lc)})"
    if isinstance(e, ast.BinOp) and type(e.op) in _ARITH:
        a = _int_expr(e.left, names, line, result, rename, lc)
        b = _int_expr(e.right, names, line, result, rename, lc)
        return f"({a} {_ARITH[type(e.op)]} {b})"
    if isinstance(e, ast.BinOp) and isinstance(e.op, ast.Pow):
        # A NEGATIVE exponent makes CPython return a float, which is
        # outside the int fragment, so the exponent carries the same
        # kind of well-formedness obligation a divisor does. Unlike a
        # divisor, zero is fine.
        if not (lc.positive(e.right) or _nonneg_literal(e.right)
                or (isinstance(e.right, ast.Name)
                    and e.right.id in lc.nonneg_names)):
            raise _reject(
                "the exponent of `**` must be a non-negative literal, or "
                "a name the contract proves non-negative — CPython "
                "returns a FLOAT for a negative exponent, which is "
                "outside this fragment", line)
        a = _int_expr(e.left, names, line, result, rename, lc)
        b = _int_expr(e.right, names, line, result, rename, lc)
        return f"(VeriPy.PyPow {a} {b})"
    if isinstance(e, ast.BinOp) and isinstance(e.op, (ast.FloorDiv, ast.Mod)):
        if not lc.positive(e.right):
            raise _reject(
                "the divisor of `//`/`%` must be a positive literal or a "
                "parameter a top-level `requires` proves positive — Python "
                "RAISES on a zero divisor while Lean's total fdiv/fmod "
                "return 0, so an undischarged divisor obligation would "
                "certify a program CPython cannot run", line)
        a = _int_expr(e.left, names, line, result, rename, lc)
        b = _int_expr(e.right, names, line, result, rename, lc)
        op = "PyFloorDiv" if isinstance(e.op, ast.FloorDiv) else "PyMod"
        return f"(VeriPy.{op} {a} {b})"
    if isinstance(e, ast.Subscript) and isinstance(e.value, ast.Name) \
            and e.value.id == "result" and result is not None:
        idx = e.slice
        if not lc.result_is_list:
            raise _reject(
                "`result[...]` needs a function that RETURNS a list — "
                "this one does not, so there is nothing to index", line)
        if lc.result_list is None:
            raise _reject(
                "`result[...]` needs an earlier `ensures` proving "
                "`len(result)` equal to a list parameter's length — "
                "without it nothing bounds the index, and Lean's total "
                "indexing would quietly read the default where Python "
                "raises IndexError", line)
        if isinstance(idx, ast.Name) \
                and lc.safe_for(idx.id, lc.result_list):
            # In bounds because an earlier clause proved `result` and
            # that list the same length.
            return f"({result}.getD ({_lref(idx.id, rename)}).toNat 0)"
        raise _reject(
            "index into `result` is not structurally in bounds — it "
            "needs an index this slice already knows is in bounds for "
            "the list an earlier `ensures` proved `result` matches",
            line)
    if isinstance(e, ast.Subscript) and isinstance(e.value, ast.Name) \
            and e.value.id in lc.lists:
        if isinstance(e.slice, ast.Slice):
            raise _reject("a list slice appears only as `sum(xs[:i])` "
                          "inside an invariant in this slice", line)
        idx = e.slice
        if isinstance(idx, ast.Name) and lc.safe_for(idx.id, e.value.id):
            # In bounds by construction, so Lean's total `getD` and
            # Python's partial indexing agree on every observed index.
            return (f"({_lref(e.value.id, rename)}.getD "
                    f"({_lref(idx.id, rename)}).toNat 0)")
        if isinstance(idx, ast.Constant) and isinstance(idx.value, int) \
                and not isinstance(idx.value, bool) \
                and lc.literal_ok(idx.value, e.value.id):
            # In bounds by CONTRACT: a top-level requires conjunct
            # bounds the length below by more than this literal.
            return f"({_lref(e.value.id, rename)}.getD {idx.value} 0)"
        raise _reject(
            f"index into {e.value.id!r} is not structurally in bounds — "
            f"this slice indexes a list only by the loop index of `for i "
            f"in range(len({e.value.id}))`, a quantifier binder over "
            f"`range(len({e.value.id}))`, or a literal below a "
            f"requires-clause length bound", line)
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name):
        args = e.args
        if e.func.id in _MATH_FNS:
            raise _reject(_MATH_LEAN, line)
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
            a = _int_expr(args[0], names, line, result, rename, lc)
            b = _int_expr(args[1], names, line, result, rename, lc)
            return f"({e.func.id} {a} {b})"
        if e.func.id == "abs" and len(args) == 1:
            # Qualified: immune to user redeclaration AND binder capture
            # (a parameter named PyAbs shadows the bare name, never the
            # namespaced one).
            return (f"(VeriPy.PyAbs "
                    f"{_int_expr(args[0], names, line, result, rename, lc)})")
        if e.func.id == "len" and len(args) == 1:
            if isinstance(args[0], ast.Name) \
                    and args[0].id == "result" and result is not None:
                if not lc.result_is_list:
                    raise _reject(
                        "`len(result)` needs a function that RETURNS a "
                        "list — this one does not, so it has no length",
                        line)
                return f"(({result}.length : Int))"
            if isinstance(args[0], ast.Name) and args[0].id in lc.lists:
                # Python len == List.length exactly (both count elements,
                # both nonnegative); the cast lands in omega's fragment.
                return f"(({_lref(args[0].id, rename)}.length : Int))"
            raise _reject("`len` applies to a list parameter only in "
                          "this slice", line)
        if e.func.id == "sum" and len(args) == 1:
            a0 = args[0]
            if isinstance(a0, ast.Name) and a0.id in lc.lists:
                # Python folds left, PySum folds right; Int addition is
                # commutative and associative, so the values agree.
                return f"(VeriPy.PySum {_lref(a0.id, rename)})"
            if isinstance(a0, ast.Subscript) \
                    and isinstance(a0.value, ast.Name) \
                    and a0.value.id in lc.lists \
                    and isinstance(a0.slice, ast.Slice):
                sl = a0.slice
                if sl.lower is None and sl.step is None \
                        and isinstance(sl.upper, ast.Name) \
                        and lc.take_idx is not None \
                        and sl.upper.id == lc.take_idx:
                    return (f"(VeriPy.PySum "
                            f"({_lref(a0.value.id, rename)}.take "
                            f"({_lref(sl.upper.id, rename)}).toNat))")
                raise _reject("only `sum(xs[:i])` with the loop index as "
                              "the slice bound is in this slice, and only "
                              "inside the loop's invariant", line)
            raise _reject("`sum` applies to a list parameter or "
                          "`xs[:i]` in this slice", line)
        if e.func.id == "old" and len(args) == 1 \
                and isinstance(args[0], ast.Name):
            # Parameters are immutable in this slice (reassignment is
            # rejected), so entry value == current value.
            return _int_expr(args[0], names, line, result, rename, lc)
        raise _reject(f"call to {e.func.id!r} is outside slice 1 "
                      f"(min/max/abs/len/sum/old only)", line)
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute) \
            and e.func.attr in _MATH_FNS:
        raise _reject(_MATH_LEAN, line)
    raise _reject(f"expression {ast.dump(e)[:60]}... is outside slice 1",
                  line)


def _quantifier(e: ast.Call, names: set[str], line: int,
                result: str | None, rename: dict[str, str] | None,
                result_is_bool: bool,
                avoid: frozenset[str] | None = None,
                lc: _ListCtx | None = None) -> str | None:
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
    if comp.ifs:
        raise _reject(
            "filtered quantifiers are outside the Lean slice — the "
            "Dafny backend admits them; write the filter as a conjunct "
            "in the body (`all(P and Q for ...)`)", line)
    if comp.is_async or not isinstance(comp.target, ast.Name):
        raise _reject("filtered or destructuring quantifier binders are "
                      "outside slice 2", line)
    it = comp.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
            and it.func.id == "range" and it.func.id not in names
            and not it.keywords and len(it.args) in (1, 2)):
        raise _reject("quantifier domains must be `range(a, b)` or "
                      "`range(b)` in slice 2 (and `range` must not be "
                      "shadowed)", line)
    lc = lc or _NO_LISTS
    if len(it.args) == 2:
        lo = _int_expr(it.args[0], names, line, result, rename, lc)
        hi = _int_expr(it.args[1], names, line, result, rename, lc)
    else:
        lo = "0"
        hi = _int_expr(it.args[0], names, line, result, rename, lc)
    v = comp.target.id
    if v in lc.lists:
        raise _reject(f"quantifier binder {v!r} shadows a list parameter "
                      f"— outside this slice", line)
    # A binder over `range(len(L))` (or `range(0, len(L))`) is in bounds
    # for L wherever the bound hypothesis guards it — which is exactly
    # the ∀-body (bound → body) and ∃-body (bound ∧ body) positions this
    # translation emits. Record the pair so the body may index L. Either
    # way the binder SHADOWS its name: an outer safe pair (or the take
    # index) under the same name refers to a different variable inside
    # the body, so it is dropped, never inherited.
    # The bound hypothesis gives `lo <= v`, so a binder over a range
    # whose lower bound is non-negative is itself non-negative — which
    # is what an exponent needs. `range(n)` and `range(0, n)` both
    # start at zero.
    body_nonneg = set(lc.nonneg_names)
    lo_arg = it.args[0] if len(it.args) == 2 else None
    if lo_arg is None or _nonneg_bound(lo_arg, lc):
        body_nonneg.add(v)
    else:
        body_nonneg.discard(v)
    safe = {k: lst for k, lst in lc.safe_idx.items() if k != v}
    hi_arg = it.args[-1]
    lo_is_zero = len(it.args) == 1 \
        or (isinstance(it.args[0], ast.Constant) and it.args[0].value == 0)
    # A binder over `range(lo, hi)` with a positive literal `lo` is
    # itself positive wherever the bound hypothesis guards it, which is
    # exactly the body. That licenses `x % d` under
    # `forall d in range(1, m)` without a contract clause.
    body_pos = set(lc.pos_names)
    if len(it.args) == 2 and _positive_bound(it.args[0], lc):
        body_pos.add(v)
    else:
        body_pos.discard(v)   # the binder SHADOWS any outer fact
    if lc.scaffold:
        safe[v] = "*"
    elif lo_is_zero and isinstance(hi_arg, ast.Call) \
            and isinstance(hi_arg.func, ast.Name) \
            and hi_arg.func.id == "len" and not hi_arg.keywords \
            and len(hi_arg.args) == 1 \
            and isinstance(hi_arg.args[0], ast.Name) \
            and hi_arg.args[0].id in lc.lists:
        safe[v] = hi_arg.args[0].id
    body_lc = _ListCtx(lc.lists, safe,
                       None if lc.take_idx == v else lc.take_idx,
                       lc.scaffold, lc.min_len, frozenset(body_pos),
                       lc.result_list, lc.result_is_list,
                       frozenset(body_nonneg))
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
                      body_rename or None, result_is_bool, body_avoid,
                      body_lc)
    bound = f"({lo} ≤ {_ident(binder)} ∧ {_ident(binder)} < {hi})"
    if e.func.id == "all":
        return f"(∀ {_ident(binder)} : Int, {bound} → {body})"
    return f"(∃ {_ident(binder)} : Int, {bound} ∧ {body})"


def _prop_operand(e: ast.expr, names: set[str]) -> ast.expr | None:
    """The proposition an operand denotes, or None if it is an integer.

    `A <==> B` reaches the encoder desugared as `bool(A) == bool(B)`, so
    a `bool(...)` wrapper around a proposition is unwrapped here. A
    `bool(...)` around an INTEGER is Python truthiness, which is a
    different operation and stays outside the slice.

    A call whose name is SHADOWED by a parameter or local is not the
    builtin — Python calls that binding — so it is declined here and
    falls through to the integer translator, which refuses it with the
    shadowing message. Reading a shadowed `bool(...)` as the builtin
    wrapper would emit an ↔ for a source expression that means
    something else entirely."""
    if isinstance(e, (ast.BoolOp, ast.Compare)):
        return e
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
        return e
    if isinstance(e, ast.Constant) and isinstance(e.value, bool):
        return e
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) \
            and e.func.id not in names:
        if e.func.id in ("all", "any"):
            return e
        if e.func.id == "bool" and len(e.args) == 1 and not e.keywords:
            return _prop_operand(e.args[0], names)
    return None


def _prop_expr(e: ast.expr, names: set[str], line: int,
               result: str | None = None,
               rename: dict[str, str] | None = None,
               result_is_bool: bool = False,
               avoid: frozenset[str] | None = None,
               lc: _ListCtx | None = None) -> str:
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
                              result_is_bool, avoid, lc)
            iff = f"(({result} = true) ↔ {prop})"
            return iff if isinstance(e.ops[0], ast.Eq) else f"(¬{iff})"
    if isinstance(e, ast.Call):
        q = _quantifier(e, names, line, result, rename, result_is_bool,
                        avoid, lc)
        if q is not None:
            return q
    if isinstance(e, ast.Compare) and len(e.ops) == 1 \
            and type(e.ops[0]) in (ast.Eq, ast.NotEq):
        lp = _prop_operand(e.left, names)
        rp = _prop_operand(e.comparators[0], names)
        if lp is not None and rp is not None:
            # Two propositions compared with `==`. Dafny gets this free
            # because its `==` on bool IS iff; in Lean, Prop equality is
            # a different (and much stronger) statement, so the contract
            # is an ↔.
            a = _prop_expr(lp, names, line, result, rename,
                           result_is_bool, avoid, lc)
            b = _prop_expr(rp, names, line, result, rename,
                           result_is_bool, avoid, lc)
            iff = f"({a} ↔ {b})"
            return iff if isinstance(e.ops[0], ast.Eq) else f"(¬{iff})"
        if (lp is None) != (rp is None):
            # Let the integer translator speak first: when the
            # non-propositional side is a SHADOWED call, its message
            # names the real cause. Only a genuine integer operand
            # earns the mixed-comparison message.
            other = e.left if lp is None else e.comparators[0]
            _int_expr(other, names, line, result, rename, lc)
            raise _reject(
                "comparing a proposition with an integer is outside this "
                "slice — Python's bool is a subtype of int, so this is "
                "legal Python whose meaning (0/1 coercion) the encoder "
                "does not model", line)
    if isinstance(e, ast.Compare):
        parts = []
        left = e.left
        for op, right in zip(e.ops, e.comparators):
            if type(op) not in _CMP:
                raise _reject("only =/≠/</≤/>/≥ comparisons are in slice 1",
                              line)
            a = _int_expr(left, names, line, result, rename, lc)
            b = _int_expr(right, names, line, result, rename, lc)
            parts.append(f"{a} {_CMP[type(op)]} {b}")
            left = right
        return "(" + " ∧ ".join(parts) + ")"
    if isinstance(e, ast.BoolOp):
        op = "∧" if isinstance(e.op, ast.And) else "∨"
        parts = [_prop_expr(v, names, line, result, rename,
                            result_is_bool, avoid, lc)
                 for v in e.values]
        return "(" + f" {op} ".join(parts) + ")"
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
        inner = _prop_expr(e.operand, names, line, result, rename,
                           result_is_bool, avoid, lc)
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


def _no_old(e: ast.expr, line: int) -> None:
    """Reject `old(...)` in EXECUTABLE positions. `old` exists only in
    spec clauses; in Python source it is a NameError at runtime, so the
    translator's spec-context erasure (old(x) -> x) would certify a
    function whose execution cannot happen."""
    for node in ast.walk(e):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == "old":
            raise _reject("`old(...)` is only meaningful in spec clauses "
                          "— in executable Python it is a NameError",
                          line)


class _SubstExprs(ast.NodeTransformer):
    """Replace free names with whole EXPRESSIONS. Used to make a loop
    body's assignments sequential: each right-hand side is rewritten
    through the updates before it, so a step reading another
    accumulator sees its NEW value, exactly as CPython executes it.
    Substituting simultaneously would model a different program."""

    def __init__(self, mapping: dict[str, ast.expr]) -> None:
        self.mapping = mapping

    def visit_Name(self, node: ast.Name) -> ast.expr:
        repl = self.mapping.get(node.id)
        if repl is None:
            return node
        return copy.deepcopy(repl)


class _SubstName(ast.NodeTransformer):
    """Rewrite free occurrences of one name (the bool accumulator) into
    the reserved name `result`, so an invariant like `b == all(...)`
    rides the SAME pinned Bool/Prop bridge as a bool ensures clause.
    Callers pre-check that `result` does not already occur and that no
    quantifier binder shadows the accumulator, so the substitution is
    capture-free."""

    def __init__(self, old: str) -> None:
        self.old = old

    def visit_Name(self, node: ast.Name) -> ast.Name:
        if node.id == self.old:
            node.id = "result"
        return node


def _reject_undecidable_quantifier(
        e: ast.expr, names: set[str], line: int,
        lc: _ListCtx | None = None) -> None:
    """Reject all/any genexps that would become ∀/∃ in a Decidable
    position (`decide`, Lean `if`). Specs stay in `_prop_expr` as Prop.

    `decide (∀ n : Int, …)` has no Decidable instance — Int is
    infinite — so wrapping the spec-side Prop encoding would fail
    elaboration rather than reject at encode time. Walk the whole
    expression: a top-level Call is not enough, and neither is a
    bool return — while conditions and early-return tests wrap
    `_prop_expr` in `decide` too."""
    for node in ast.walk(e):
        if isinstance(node, ast.Call):
            q = _quantifier(node, names, line, None, None, False, None, lc)
            if q is not None:
                raise _reject(
                    "all/any cannot be decided in the Lean slice — "
                    "`decide` has no instance for unbounded ∀/∃ over "
                    "Int; the Dafny backend admits them as forall/"
                    "exists",
                    line)


def _bool_expr(e: ast.expr, names: set[str], line: int,
               lc: _ListCtx | None = None) -> str:
    """A Bool-valued Lean term for a predicate function's return.

    `decide` bridges the translated Prop into Bool; True/False literals
    map directly. Anything else (a bool-typed local, a bool call) is
    outside slice 2."""
    if isinstance(e, ast.Constant) and e.value is True:
        return "true"
    if isinstance(e, ast.Constant) and e.value is False:
        return "false"
    _reject_undecidable_quantifier(e, names, line, lc)
    if isinstance(e, (ast.Compare, ast.BoolOp, ast.UnaryOp)):
        return f"(decide {_prop_expr(e, names, line, lc=lc)})"
    raise _reject("a bool return must be True/False or a boolean "
                  "expression in slice 2", line)


def _list_expr(e: ast.expr, names: set[str], line: int,
               lc: _ListCtx) -> str:
    """A `List Int`-valued Lean term. `[f(x) for x in xs]` becomes
    `xs.map (fun x => f x)`, which is the same order and length as
    Python's comprehension. Filtered comprehensions change the length
    and stay out of this slice."""
    if isinstance(e, ast.Name) and e.id in lc.lists:
        return _ident(e.id)
    if isinstance(e, ast.ListComp):
        if len(e.generators) != 1:
            raise _reject("only one comprehension generator in this "
                          "slice", line)
        comp = e.generators[0]
        if comp.ifs or comp.is_async:
            raise _reject("a FILTERED comprehension changes the list's "
                          "length, which this slice does not model",
                          line)
        if not isinstance(comp.target, ast.Name):
            raise _reject("destructuring comprehension targets are "
                          "outside this slice", line)
        if not (isinstance(comp.iter, ast.Name)
                and comp.iter.id in lc.lists):
            raise _reject("a comprehension iterates a list parameter in "
                          "this slice", line)
        v = comp.target.id
        if v in names:
            raise _reject(f"comprehension binder {v!r} shadows a name in "
                          f"scope — outside this slice", line)
        body = _int_expr(e.elt, names | {v}, line, lc=lc)
        return f"({_ident(comp.iter.id)}.map (fun {_ident(v)} => {body}))"
    raise _reject("a list return must be a list parameter or a "
                  "comprehension over one in this slice", line)


def _body_expr(stmts: list[ast.stmt], names: set[str],
               params: tuple[str, ...], is_bool: bool = False,
               lc: _ListCtx | None = None, is_list: bool = False) -> str:
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
        _no_old(head.value, head.lineno)
        if is_list:
            return _list_expr(head.value, names, head.lineno,
                              lc or _NO_LISTS)
        if is_bool:
            return _bool_expr(head.value, names, head.lineno, lc)
        return _int_expr(head.value, names, head.lineno, lc=lc)
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
        _no_old(head.value, head.lineno)
        value = _int_expr(head.value, names, head.lineno, lc=lc)
        return (f"let {_ident(target)} := {value}; "
                + _body_expr(rest, names | {target}, params, is_bool, lc,
                             is_list))
    if isinstance(head, ast.If):
        _no_old(head.test, head.lineno)
        _reject_undecidable_quantifier(head.test, names, head.lineno, lc)
        cond = _prop_expr(head.test, names, head.lineno, lc=lc)
        then = _body_expr(head.body, names, params, is_bool, lc,
                          is_list)
        if head.orelse:
            if rest:
                raise _reject("unreachable code after an if/else in which "
                              "both branches return", rest[0].lineno)
            other = _body_expr(head.orelse, names, params, is_bool, lc,
                               is_list)
        else:
            if not _always_returns(head.body):
                raise _reject("an `if` without `else` must return in its "
                              "body (slice 1 compiles it to a conditional "
                              "expression)", head.lineno)
            other = _body_expr(rest, names, params, is_bool, lc,
                               is_list)
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


@dataclass
class _LoopShape:
    """One `for i in range(N)` accumulator loop (P2 slice 1).

    Python shape:  acc = INIT ; for i in range(N): acc = STEP ; return RET
    Lean shape:    fuel recursion on Nat (structurally terminating, so no
    `termination_by`), the invariant as a generated Prop, and an
    induction theorem whose inductive step IS the invariant-preservation
    VC — omega-dischargeable when invariant and step are linear.

    With `acc_bool` (P2 slice 3), the accumulator is a Bool: INIT is a
    True/False literal, STEP is `acc and P` / `acc or P` (the
    below_threshold / contains classes), RET is the bare accumulator,
    and the invariant's `acc == all(...)` becomes
    `(acc = true) ↔ ∀ ...` — proved by a generated constructor script
    whose inductive step splits the fresh index off the prefix.
    """

    index: str          # the range variable
    acc: str            # the single accumulator
    init: ast.expr      # acc's initializer (params only)
    bound: ast.expr     # range's bound N (params only)
    step: ast.expr      # the accumulator update (params, index, acc)
    ret: ast.expr       # the return expression (params, acc; NOT index)
    inv: ast.expr       # the single #@ invariant (params, index, acc)
    inv_line: int
    for_line: int
    acc_bool: bool      # Bool accumulator (True/False init, and/or step)
    acc_list: bool = False   # List accumulator (`[]` init, append step)


def _requires_min_len(spec_fn: FunctionSpec,
                      lists: frozenset[str]) -> dict[str, int]:
    """Scan TOP-LEVEL requires conjuncts for `len(L) > c` / `len(L) >=
    c` shapes (either orientation) and record the implied length lower
    bound. Top-level only: under a `not` or an `or` the comparison
    stops being a guarantee."""
    bounds: dict[str, int] = {}

    def _len_of(e: ast.expr) -> str | None:
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) \
                and e.func.id == "len" and not e.keywords \
                and len(e.args) == 1 and isinstance(e.args[0], ast.Name) \
                and e.args[0].id in lists:
            return e.args[0].id
        return None

    def _record(lst: str, bound: int) -> None:
        bounds[lst] = max(bounds.get(lst, 0), bound)

    def _conjunct(e: ast.expr) -> None:
        if isinstance(e, ast.BoolOp) and isinstance(e.op, ast.And):
            for v in e.values:
                _conjunct(v)
            return
        if not (isinstance(e, ast.Compare) and len(e.ops) == 1):
            return
        left, op, right = e.left, e.ops[0], e.comparators[0]
        lst, c = _len_of(left), right
        if lst is not None and isinstance(c, ast.Constant) \
                and isinstance(c.value, int):
            if isinstance(op, ast.Gt):
                _record(lst, c.value + 1)
            elif isinstance(op, ast.GtE):
                _record(lst, c.value)
        lst, c = _len_of(right), left
        if lst is not None and isinstance(c, ast.Constant) \
                and isinstance(c.value, int):
            if isinstance(op, ast.Lt):
                _record(lst, c.value + 1)
            elif isinstance(op, ast.LtE):
                _record(lst, c.value)

    for clause in spec_fn.by_kind("requires"):
        text = clause.desugared if clause.desugared is not None \
            else clause.raw
        try:
            _conjunct(ast.parse(text, mode="eval").body)
        except SyntaxError:
            continue  # the clause parser rejects it loudly later
    return bounds


def _positive_bound(e: ast.expr, lc: "_ListCtx") -> bool:
    """Is this range lower bound provably >= 1, so binders above it are
    positive? A literal, a name the context already knows positive, or
    either of those plus a non-negative literal — which is what
    `range(result + 1, m)` needs once `result >= 1` is established by an
    earlier clause."""
    if isinstance(e, ast.Constant) and isinstance(e.value, int) \
            and not isinstance(e.value, bool):
        return e.value >= 1
    if isinstance(e, ast.Name):
        return e.id in lc.pos_names
    if isinstance(e, ast.BinOp) and isinstance(e.op, ast.Add):
        for a, b in ((e.left, e.right), (e.right, e.left)):
            if isinstance(b, ast.Constant) and isinstance(b.value, int) \
                    and not isinstance(b.value, bool) and b.value >= 0:
                if _positive_bound(a, lc) or (b.value >= 1
                                              and _nonneg_bound(a, lc)):
                    return True
    return False


def _nonneg_bound(e: ast.expr, lc: "_ListCtx") -> bool:
    """Is this expression provably >= 0? A literal speaks for itself, a
    name the contract proves non-negative counts, and positive implies
    non-negative. The middle case was missing, so `range(lo, n)` under
    `requires lo >= 0` did not mark its binder non-negative and a valid
    `2 ** j` in the body was refused."""
    if isinstance(e, ast.Constant) and isinstance(e.value, int) \
            and not isinstance(e.value, bool):
        return e.value >= 0
    if isinstance(e, ast.Name) and e.id in lc.nonneg_names:
        return True
    if isinstance(e, ast.BinOp) and isinstance(e.op, ast.Add):
        # `lo + k` is non-negative when both parts are.
        return (_nonneg_bound(e.left, lc)
                and _nonneg_bound(e.right, lc))
    return _positive_bound(e, lc)


def _result_length_match(e: ast.expr,
                         lists: frozenset[str]) -> str | None:
    """If this clause says `len(result) == len(X)` (either way round),
    the list X whose length `result` matches. That licenses `result[i]`
    for indices already known in bounds for X — the list analogue of the
    positivity a clause hands to the clauses after it."""
    if not (isinstance(e, ast.Compare) and len(e.ops) == 1
            and isinstance(e.ops[0], ast.Eq)):
        return None

    def _len_of(x: ast.expr) -> str | None:
        if isinstance(x, ast.Call) and isinstance(x.func, ast.Name) \
                and x.func.id == "len" and not x.keywords \
                and len(x.args) == 1 and isinstance(x.args[0], ast.Name):
            return x.args[0].id
        return None

    a, b = _len_of(e.left), _len_of(e.comparators[0])
    if a == "result" and b in lists:
        return b
    if b == "result" and a in lists:
        return a
    return None


def _sign_facts(e: ast.expr) -> tuple[set[str], set[str], set[str]]:
    """(nonneg, nonzero, positive) names a conjunction of comparisons
    establishes. Only TOP-LEVEL conjuncts count: under a `not` or an
    `or` the comparison stops being a guarantee."""
    nonneg: set[str] = set()
    nonzero: set[str] = set()
    positive: set[str] = set()

    def walk(x: ast.expr) -> None:
        if isinstance(x, ast.BoolOp) and isinstance(x.op, ast.And):
            for v in x.values:
                walk(v)
            return
        if not isinstance(x, ast.Compare):
            return
        # Chained comparisons (`0 <= i <= n`) are conjunctions.
        left = x.left
        for op, right in zip(x.ops, x.comparators):
            for a, o, b in ((left, op, right),):
                if isinstance(a, ast.Name) and isinstance(b, ast.Constant) \
                        and isinstance(b.value, int) \
                        and not isinstance(b.value, bool):
                    c = b.value
                    if isinstance(o, ast.GtE) and c >= 0:
                        nonneg.add(a.id)
                        if c >= 1:
                            positive.add(a.id)
                    elif isinstance(o, ast.Gt) and c >= -1:
                        nonneg.add(a.id)
                        if c >= 0:
                            positive.add(a.id)
                    elif isinstance(o, ast.NotEq) and c == 0:
                        nonzero.add(a.id)
                    elif isinstance(o, ast.Eq) and c >= 1:
                        positive.add(a.id)
                if isinstance(b, ast.Name) and isinstance(a, ast.Constant) \
                        and isinstance(a.value, int) \
                        and not isinstance(a.value, bool):
                    c = a.value
                    if isinstance(o, ast.LtE) and c >= 0:
                        nonneg.add(b.id)
                        if c >= 1:
                            positive.add(b.id)
                    elif isinstance(o, ast.Lt) and c >= -1:
                        nonneg.add(b.id)
                        if c >= 0:
                            positive.add(b.id)
                    elif isinstance(o, ast.NotEq) and c == 0:
                        nonzero.add(b.id)
                    elif isinstance(o, ast.Eq) and c >= 1:
                        positive.add(b.id)
            left = right

    walk(e)
    return nonneg, nonzero, positive


def _nonneg_literal(e: ast.expr) -> bool:
    return (isinstance(e, ast.Constant) and isinstance(e.value, int)
            and not isinstance(e.value, bool) and e.value >= 0)


def _requires_nonneg(spec_fn: FunctionSpec) -> frozenset[str]:
    """Names a top-level `requires` conjunct proves >= 0."""
    out: set[str] = set()
    for clause in spec_fn.by_kind("requires"):
        text = clause.desugared if clause.desugared is not None else clause.raw
        try:
            nn, _, pos = _sign_facts(ast.parse(text, mode="eval").body)
        except SyntaxError:
            continue
        out |= nn | pos
    return frozenset(out)


def _requires_positive(spec_fn: FunctionSpec) -> frozenset[str]:
    """Names a TOP-LEVEL `requires` conjunct proves strictly positive
    (`p > c` for c >= 0, `p >= c` for c >= 1, and the mirrored forms).
    Top-level only: under a `not` or an `or` the comparison stops being
    a guarantee — the same discipline as the length scan."""
    out: set[str] = set()

    def _conjunct(e: ast.expr) -> None:
        if isinstance(e, ast.BoolOp) and isinstance(e.op, ast.And):
            for v in e.values:
                _conjunct(v)
            return
        if not (isinstance(e, ast.Compare) and len(e.ops) == 1):
            return
        left, op, right = e.left, e.ops[0], e.comparators[0]
        if isinstance(left, ast.Name) and isinstance(right, ast.Constant) \
                and isinstance(right.value, int) \
                and not isinstance(right.value, bool):
            if (isinstance(op, ast.Gt) and right.value >= 0) \
                    or (isinstance(op, ast.GtE) and right.value >= 1):
                out.add(left.id)
        if isinstance(right, ast.Name) and isinstance(left, ast.Constant) \
                and isinstance(left.value, int) \
                and not isinstance(left.value, bool):
            if (isinstance(op, ast.Lt) and left.value >= 0) \
                    or (isinstance(op, ast.LtE) and left.value >= 1):
                out.add(right.id)

    for clause in spec_fn.by_kind("requires"):
        text = clause.desugared if clause.desugared is not None else clause.raw
        try:
            _conjunct(ast.parse(text, mode="eval").body)
        except SyntaxError:
            continue  # the clause parser rejects it loudly later
    return frozenset(out)


def _divmod_sites(fn: ast.FunctionDef,
                  spec_fn: FunctionSpec) -> list[tuple[ast.expr, ast.expr, bool]]:
    """Every `//`/`%` node in the body and the spec clauses, as
    (dividend, divisor, is_mod). The generated proof supplies each site's
    positivity fact and mod bounds, because omega reasons about `%`
    natively ONLY for constant divisors (measured)."""
    trees: list[ast.AST] = [fn]
    for kind in ("requires", "ensures", "invariant"):
        for clause in spec_fn.by_kind(kind):
            text = clause.desugared if clause.desugared is not None \
                else clause.raw
            try:
                trees.append(ast.parse(text, mode="eval").body)
            except SyntaxError:
                continue
    sites: list[tuple[ast.expr, ast.expr, bool]] = []
    for tree in trees:
        for node in ast.walk(tree):
            if isinstance(node, ast.BinOp) \
                    and isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                sites.append((node.left, node.right,
                              isinstance(node.op, ast.Mod)))
    return sites


def _loop_invariants(spec_fn: FunctionSpec,
                     loop: ast.For | ast.While) -> tuple[ast.expr, int]:
    """Collect every `#@ invariant` at the loop HEAD and conjoin them
    (slice 5: max_element-class tasks state a prefix bound AND a
    witness). One generated Prop carries the conjunction; the
    preservation script splits it constructor-wise.

    Placement is the Dafny backend's rule verbatim: strictly between
    the `for` header and the first body statement (loop-head
    semantics). With multi-statement bodies, an invariant deeper in
    the span is REJECTED, not silently adopted or ignored — the
    encoder would otherwise accept source the documented fragment and
    the sibling backend refuse."""
    every = spec_fn.by_kind("invariant")
    invs = [c for c in every
            if loop.lineno < c.line < loop.body[0].lineno]
    misplaced = [c for c in every if c not in invs]
    if misplaced:
        # This slice admits one loop per function, so EVERY invariant
        # in the function must sit at that loop's head — a stray one
        # anywhere else would otherwise be silently ignored.
        raise _reject("`invariant` must sit at the top of the loop "
                      "body, before its first statement (Dafny "
                      "loop-head semantics — the same rule the "
                      "conformance backend enforces)",
                      misplaced[0].line)
    if not invs:
        raise _reject("a loop needs at least one `#@ invariant` in this "
                      "slice", loop.lineno)
    parsed = []
    for c in invs:
        text = c.desugared if c.desugared is not None else c.raw
        try:
            parsed.append(ast.parse(text, mode="eval").body)
        except SyntaxError as exc:
            raise _reject(f"cannot parse invariant: {exc.msg}", c.line)
    if len(parsed) == 1:
        return parsed[0], invs[0].line
    expr = ast.BoolOp(op=ast.And(), values=parsed)
    ast.copy_location(expr, parsed[0])
    ast.fix_missing_locations(expr)
    return expr, invs[0].line


def _early_return_loop(stmts: list[ast.stmt], fn: ast.FunctionDef,
                       spec_fn: FunctionSpec) -> _LoopShape | None:
    """Match `for i in range(N): if TEST: return V; return W` (V, W
    complementary bool literals) — the search-loop shape HumanEval
    favors (below_threshold, contains-style membership).

    Python short-circuits at the first hit; the fold model runs every
    index. The RESULT is identical (Bool `or`/`and` are monotone and
    the body is pure), so the desugaring into the slice-3 accumulator
    machinery is faithful: `return True` on hit is the or-accumulator
    over TEST, `return False` on hit is the and-accumulator over
    not-TEST. The invariant mentions no accumulator in this shape, so
    it becomes the iff-body of a synthesized one."""
    if len(stmts) != 2 or not isinstance(stmts[0], ast.For) \
            or not isinstance(stmts[1], ast.Return):
        return None
    loop, ret_stmt = stmts
    body = list(loop.body)
    if len(body) != 1 or not isinstance(body[0], ast.If) \
            or body[0].orelse or len(body[0].body) != 1 \
            or not isinstance(body[0].body[0], ast.Return):
        return None
    hit_ret = body[0].body[0].value
    end_ret = ret_stmt.value
    if not (isinstance(hit_ret, ast.Constant)
            and isinstance(hit_ret.value, bool)
            and isinstance(end_ret, ast.Constant)
            and isinstance(end_ret.value, bool)):
        raise _reject("an early-return loop returns bool literals in "
                      "this slice", loop.lineno)
    if hit_ret.value == end_ret.value:
        raise _reject("the early return and the final return must "
                      "differ (a constant function needs no loop)",
                      loop.lineno)
    if not isinstance(loop.target, ast.Name):
        raise _reject(
            "destructuring loop targets are outside the Lean slice — the "
            "Dafny backend admits `for a, b in pairs` over a list of "
            "tuples; this slice's fuel recursion binds one index",
            loop.lineno)
    it = loop.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
            and it.func.id == "range" and len(it.args) == 1
            and not it.keywords):
        raise _reject("loops must iterate `range(<bound>)` in this slice",
                      loop.lineno)
    if loop.orelse:
        raise _reject("`for ... else` is outside the fragment", loop.lineno)
    test = body[0].test
    _no_old(test, body[0].lineno)
    index = loop.target.id
    # A fresh accumulator name: never a source binding, so freshness
    # only needs to dodge every name the function or its spec mentions.
    used = {index} | {a.arg for a in fn.args.args}
    for node in ast.walk(fn):
        if isinstance(node, ast.Name):
            used.add(node.id)
    acc = "b"
    while acc in used:
        acc += "'"
    if hit_ret.value:  # return True on hit: any(TEST) — or-accumulator
        step: ast.expr = ast.BoolOp(
            op=ast.Or(), values=[ast.Name(id=acc, ctx=ast.Load()), test])
    else:              # return False on hit: all(not TEST) — and-acc
        step = ast.BoolOp(op=ast.And(),
                          values=[ast.Name(id=acc, ctx=ast.Load()),
                                  ast.UnaryOp(op=ast.Not(), operand=test)])
    ast.copy_location(step, test)
    ast.fix_missing_locations(step)
    inv_expr, inv_line = _loop_invariants(spec_fn, loop)
    for node in ast.walk(inv_expr):
        if isinstance(node, ast.Name) and node.id == acc:
            raise _reject(f"synthesized accumulator {acc!r} collides "
                          f"inside the invariant", inv_line)
    # The user's invariant states the still-searching prefix property;
    # the synthesized accumulator tracks exactly that, so the generated
    # invariant is their iff (`acc == <inv>` through the Bool bridge).
    wrapped = ast.Compare(left=ast.Name(id=acc, ctx=ast.Load()),
                          ops=[ast.Eq()], comparators=[inv_expr])
    ast.copy_location(wrapped, inv_expr)
    ast.fix_missing_locations(wrapped)
    return _LoopShape(index=index, acc=acc,
                      init=ast.Constant(value=end_ret.value),
                      bound=it.args[0], step=step,
                      ret=ast.Name(id=acc, ctx=ast.Load()),
                      inv=wrapped,
                      inv_line=inv_line, for_line=loop.lineno,
                      acc_bool=True)


@dataclass
class _WhileShape:
    """One `while COND:` loop over N accumulators (P2 slices 7-8).

    Python shape:  a1 = e1 ; ... ; aN = eN ; while COND: <body> ; return RET
    Lean shape:    fuel recursion whose fuel is the `#@ decreases`
    MEASURE. With N > 1 the loop state is a tuple and the theorem reads
    it back through projections.

    The body's assignments are SEQUENTIAL, so `steps` keeps them in
    order and each right-hand side is translated through a substitution
    map: a later statement sees the earlier updates, exactly as CPython
    executes them. Translating them simultaneously would model a
    different program whenever one accumulator's update reads another's
    new value.
    """

    accs: list[str]
    inits: list[ast.expr]
    cond: ast.expr
    # Each GROUP is applied simultaneously; groups run in order. A plain
    # `x = e` is a group of one, while `x, y = y, x` is a single group
    # of two — Python evaluates a tuple assignment's whole right side
    # before binding anything, so a swap really swaps. Treating that as
    # two sequential assignments would model a different program.
    steps: list[list[tuple[str, ast.expr]]]
    ret: ast.expr
    inv: ast.expr
    inv_line: int
    meas: ast.expr
    meas_line: int
    while_line: int


def _proj(k: int, n: int) -> str:
    """Projection onto accumulator k of an n-tuple. Lean's `×` is
    right-associative, so `(a, b, c)` is `(a, (b, c))`."""
    if n == 1:
        return ""
    return ".2" * k + (".1" if k < n - 1 else "")


def _infer_measure(cond: ast.expr) -> ast.expr | None:
    """A termination measure read off the loop condition: `i < n` counts
    down as `n - i`, `x > y` as `x - y`, and `y != 0` as `y`. Only a
    proposal — the induction theorem still has to prove it decreases and
    stays non-negative, so a bad guess costs a failed proof, never a
    false one."""
    if not (isinstance(cond, ast.Compare) and len(cond.ops) == 1):
        return None
    left, op, right = cond.left, cond.ops[0], cond.comparators[0]
    # An INCLUSIVE comparison needs one more than the difference. With
    # `while i <= n`, the measure `n - i` reaches zero while the
    # condition is still true, so a fuel recursion runs out one step
    # early. Dafny accepts `n - i` because its rule is
    # decrease-and-bounded per iteration; a fuel model needs the
    # iteration COUNT, which is one larger.
    slack = 0
    if isinstance(op, (ast.Lt, ast.LtE)):
        hi, lo = right, left
        slack = 1 if isinstance(op, ast.LtE) else 0
    elif isinstance(op, (ast.Gt, ast.GtE)):
        hi, lo = left, right
        slack = 1 if isinstance(op, ast.GtE) else 0
    elif isinstance(op, ast.NotEq) and _nonneg_literal(right):
        return cond.left
    elif isinstance(op, ast.NotEq) and _nonneg_literal(left):
        return cond.comparators[0]
    else:
        return None
    out: ast.expr = ast.BinOp(left=hi, op=ast.Sub(), right=lo)
    if slack:
        out = ast.BinOp(left=out, op=ast.Add(),
                        right=ast.Constant(value=slack))
    ast.copy_location(out, cond)
    ast.fix_missing_locations(out)
    return out


def _loop_decreases(spec_fn: FunctionSpec,
                    loop: ast.While) -> tuple[ast.expr, int]:
    """The single `#@ decreases` measure at the loop head. Placement is
    the invariant rule verbatim, and the clause is REQUIRED: without a
    measure there is no fuel bound, so nothing rules out a loop that
    silently stops early."""
    every = spec_fn.by_kind("decreases")
    at_head = [c for c in every
               if loop.lineno < c.line < loop.body[0].lineno]
    misplaced = [c for c in every if c not in at_head]
    if misplaced:
        raise _reject("`decreases` must sit at the top of the loop body, "
                      "before its first statement", misplaced[0].line)
    if not at_head:
        # No clause: infer one from the condition. This is SAFE rather
        # than clever — the generated theorem still proves that the
        # measure decreases and stays bounded below, so a wrong guess
        # fails honestly instead of admitting a loop that never ends.
        # Dafny infers here too, and the frozen corpus relies on it.
        inferred = _infer_measure(loop.test)
        if inferred is None:
            raise _reject(
                "a `while` loop needs a `#@ decreases` measure here — "
                "one could not be inferred from the condition, and "
                "without a measure a loop that stops early cannot be "
                "ruled out", loop.lineno)
        return inferred, loop.lineno
    if len(at_head) != 1:
        raise _reject("a `while` loop needs exactly one `#@ decreases` "
                      f"measure in this slice (found {len(at_head)}) — "
                      f"the measure is the loop's fuel bound, and without "
                      f"it a loop that stops early cannot be ruled out",
                      loop.lineno)
    clause = at_head[0]
    text = clause.desugared if clause.desugared is not None else clause.raw
    try:
        return ast.parse(text, mode="eval").body, clause.line
    except SyntaxError as exc:
        raise _reject(f"cannot parse decreases: {exc.msg}", clause.line)


def _squared_terms(exprs: list[ast.expr]) -> list[ast.expr]:
    """Unique `X` such that `X * X` occurs. omega is linear and core Lean
    has no nlinarith, so a squaring loop stalls without the prelude's
    SqGeSelf; these are the instances worth handing it."""
    out: list[ast.expr] = []
    seen: set[str] = set()
    for e in exprs:
        for node in ast.walk(e):
            if isinstance(node, ast.BinOp) \
                    and isinstance(node.op, ast.Mult) \
                    and ast.dump(node.left) == ast.dump(node.right):
                key = ast.dump(node.left)
                if key not in seen:
                    seen.add(key)
                    out.append(node.left)
    return out


def _split_while(fn: ast.FunctionDef,
                 spec_fn: FunctionSpec) -> _WhileShape:
    """Match the while shape, or REJECT loudly. Only called once a
    `while` is known to be present, so returning None would just hand
    the body compiler a worse message."""
    stmts = [st for st in fn.body
             if not (isinstance(st, ast.Expr)
                     and isinstance(st.value, ast.Constant))]
    whiles = [st for st in stmts if isinstance(st, ast.While)]
    if len(whiles) != 1 or any(isinstance(n, ast.While)
                               for st in stmts if st is not whiles[0]
                               for n in ast.walk(st)):
        raise _reject("one `while` loop per function in this slice",
                      whiles[0].lineno if whiles else fn.lineno)
    loop = whiles[0]
    idx = stmts.index(loop)
    inits_stmts, rest = stmts[:idx], stmts[idx + 1:]
    if not inits_stmts or len(rest) != 1 \
            or not isinstance(rest[0], ast.Return):
        raise _reject("a `while` function must be `acc = init` (one or "
                      "more) then `while ...: ...` then `return expr` in "
                      "this slice", loop.lineno)
    ret_stmt = rest[0]
    accs: list[str] = []
    inits: list[ast.expr] = []
    for st in inits_stmts:
        if isinstance(st, ast.AnnAssign):
            if not (isinstance(st.target, ast.Name)
                    and isinstance(st.annotation, ast.Name)
                    and st.annotation.id == "int" and st.value is not None):
                raise _reject("an annotated accumulator initializer must "
                              "be `name: int = <expr>`", st.lineno)
            target, value = st.target.id, st.value
        elif isinstance(st, ast.Assign) and len(st.targets) == 1 \
                and isinstance(st.targets[0], ast.Tuple):
            tgt, val = st.targets[0], st.value
            if not isinstance(val, ast.Tuple) \
                    or len(tgt.elts) != len(val.elts):
                raise _reject("a tuple initializer must bind a tuple of "
                              "the same length (`x, y = a, b`)",
                              st.lineno)
            if not all(isinstance(e, ast.Name) for e in tgt.elts):
                raise _reject("tuple initializer targets must be plain "
                              "names", st.lineno)
            for nm, v in zip(tgt.elts, val.elts):
                if nm.id in accs:
                    raise _reject(f"accumulator {nm.id!r} is initialized "
                                  f"twice", st.lineno)
                accs.append(nm.id)
                inits.append(v)
            continue
        elif isinstance(st, ast.Assign):
            if len(st.targets) != 1 \
                    or not isinstance(st.targets[0], ast.Name):
                raise _reject("the accumulator initializer must assign "
                              "one name", st.lineno)
            target, value = st.targets[0].id, st.value
        else:
            raise _reject(f"`{type(st).__name__}` before a `while` is "
                          f"outside this slice (accumulator "
                          f"initializers only)", st.lineno)
        if target in accs:
            raise _reject(f"accumulator {target!r} is initialized twice",
                          st.lineno)
        if isinstance(value, ast.Constant) \
                and isinstance(value.value, bool):
            raise _reject("bool accumulators are outside the `while` "
                          "slice (integer measures and accumulators "
                          "only)", st.lineno)
        accs.append(target)
        inits.append(value)
    if loop.orelse:
        raise _reject("`while ... else` is outside the fragment",
                      loop.lineno)
    steps: list[list[tuple[str, ast.expr]]] = []
    for st in loop.body:
        if not isinstance(st, ast.Assign) or len(st.targets) != 1:
            raise _reject("the loop body must be assignments to the "
                          "accumulators in this slice",
                          getattr(st, "lineno", loop.lineno))
        tgt = st.targets[0]
        if isinstance(tgt, ast.Tuple):
            val = st.value
            if not isinstance(val, ast.Tuple) \
                    or len(tgt.elts) != len(val.elts):
                raise _reject("a tuple assignment must assign a tuple of "
                              "the same length (`x, y = y, x % y`)",
                              st.lineno)
            if not all(isinstance(e, ast.Name) for e in tgt.elts):
                raise _reject("tuple assignment targets must be plain "
                              "names", st.lineno)
            group = [(e.id, v) for e, v in zip(tgt.elts, val.elts)]
            seen_t = {n for n, _ in group}
            if len(seen_t) != len(group):
                raise _reject("a tuple assignment must not bind the same "
                              "name twice", st.lineno)
        elif isinstance(tgt, ast.Name):
            group = [(tgt.id, st.value)]
        else:
            raise _reject("the loop body must be single-name or tuple "
                          "assignments to the accumulators in this "
                          "slice", st.lineno)
        for name, _ in group:
            if name not in accs:
                raise _reject(f"the loop body assigns {name!r}, which is "
                              f"not one of the accumulators "
                              f"({', '.join(accs)})", st.lineno)
        steps.append(group)
    if not steps:
        raise _reject("the loop body must assign at least one "
                      "accumulator", loop.lineno)
    if ret_stmt.value is None:
        raise _reject("bare `return` has no value to encode",
                      ret_stmt.lineno)
    inv_expr, inv_line = _loop_invariants(spec_fn, loop)
    meas_expr, meas_line = _loop_decreases(spec_fn, loop)
    for expr, ln in ([(v, fn.lineno) for v in inits]
                     + [(loop.test, loop.lineno)]
                     + [(v, loop.lineno) for g in steps for _, v in g]
                     + [(ret_stmt.value, ret_stmt.lineno)]):
        _no_old(expr, ln)
    return _WhileShape(accs=accs, inits=inits, cond=loop.test, steps=steps,
                       ret=ret_stmt.value, inv=inv_expr, inv_line=inv_line,
                       meas=meas_expr, meas_line=meas_line,
                       while_line=loop.lineno)


def _split_loop(fn: ast.FunctionDef,
                spec_fn: FunctionSpec) -> _LoopShape | None:
    """Match the P2 slice-1 loop shape, or None for the loop-free path.
    A `for` that does not fit the shape is REJECTED (not silently routed
    to the loop-free compiler, which would refuse it with a worse
    message)."""
    stmts = [s for s in fn.body
             if not (isinstance(s, ast.Expr)
                     and isinstance(s.value, ast.Constant))]
    fors = [s for s in stmts if isinstance(s, ast.For)]
    if not fors:
        return None
    if len(fors) > 1:
        raise _reject("one loop per function in this slice", fors[1].lineno)
    early = _early_return_loop(stmts, fn, spec_fn)
    if early is not None:
        return early
    if len(stmts) != 3 or not isinstance(stmts[0], (ast.Assign,
                                                    ast.AnnAssign)) \
            or not isinstance(stmts[1], ast.For) \
            or not isinstance(stmts[2], ast.Return):
        raise _reject("a loop function must be exactly `acc = init; "
                      "for ...: ...; return expr` (or an early-return "
                      "search loop) in this slice", fors[0].lineno)
    init_stmt, loop, ret_stmt = stmts
    if isinstance(init_stmt, ast.AnnAssign):
        # `m: int = l[0]` — the annotation must be `int` (the only
        # accumulator type an annotation can spell; bool accumulators
        # are recognized by their True/False literal), and the value
        # must be present.
        ann = init_stmt.annotation
        ann_ok = ((isinstance(ann, ast.Name) and ann.id == "int")
                  or (isinstance(ann, ast.Subscript)
                      and isinstance(ann.value, ast.Name)
                      and ann.value.id == "list"
                      and isinstance(ann.slice, ast.Name)
                      and ann.slice.id == "int"))
        if not (isinstance(init_stmt.target, ast.Name) and ann_ok
                and init_stmt.value is not None):
            raise _reject("an annotated accumulator initializer must be "
                          "`name: int = <expr>`", init_stmt.lineno)
        init_value, acc = init_stmt.value, init_stmt.target.id
    else:
        if len(init_stmt.targets) != 1 \
                or not isinstance(init_stmt.targets[0], ast.Name):
            raise _reject("the accumulator initializer must assign one "
                          "name", init_stmt.lineno)
        init_value, acc = init_stmt.value, init_stmt.targets[0].id
    if not isinstance(loop.target, ast.Name):
        raise _reject(
            "destructuring loop targets are outside the Lean slice — the "
            "Dafny backend admits `for a, b in pairs` over a list of "
            "tuples; this slice's fuel recursion binds one index",
            loop.lineno)
    index = loop.target.id
    it = loop.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
            and it.func.id == "range" and len(it.args) == 1
            and not it.keywords):
        raise _reject("loops must iterate `range(<bound>)` in this slice",
                      loop.lineno)
    if loop.orelse:
        raise _reject("`for ... else` is outside the fragment", loop.lineno)
    body = [s for s in loop.body]
    step_expr: ast.expr | None = None
    if len(body) == 1 and isinstance(body[0], ast.If) \
            and not body[0].orelse and len(body[0].body) == 1 \
            and isinstance(body[0].body[0], ast.Assign):
        # Conditional update `if TEST: acc = E` (slice 5). The only
        # recognized forms are the max/min guards — TEST compares E
        # against the accumulator — because those compile to `max`/
        # `min`, which omega reasons about natively; an `if-then-else`
        # term in the step would sit inside the loop atom where no
        # tactic in the fixed cocktail can split it.
        upd = body[0].body[0]
        if not (len(upd.targets) == 1
                and isinstance(upd.targets[0], ast.Name)
                and upd.targets[0].id == acc):
            raise _reject(f"a conditional loop body updates the "
                          f"accumulator {acc!r} in this slice",
                          loop.lineno)
        test, e_new = body[0].test, upd.value
        fn_name = None
        if isinstance(test, ast.Compare) and len(test.ops) == 1:
            lhs, op, rhs = test.left, test.ops[0], test.comparators[0]
            e_d = ast.dump(e_new)
            if ast.dump(lhs) == e_d and isinstance(rhs, ast.Name) \
                    and rhs.id == acc:
                # if E (>|>=) acc: acc = E  → max ; (<|<=) → min
                fn_name = {ast.Gt: "max", ast.GtE: "max",
                           ast.Lt: "min", ast.LtE: "min"}.get(type(op))
            elif isinstance(lhs, ast.Name) and lhs.id == acc \
                    and ast.dump(rhs) == e_d:
                # if acc (<|<=) E: acc = E  → max ; (>|>=) → min
                fn_name = {ast.Lt: "max", ast.LtE: "max",
                           ast.Gt: "min", ast.GtE: "min"}.get(type(op))
        if fn_name is None:
            raise _reject(
                "a conditional update must be max/min-shaped in this "
                "slice (`if E > acc: acc = E` or a mirrored form)",
                loop.lineno)
        for node in ast.walk(e_new):
            if isinstance(node, ast.Name) and node.id == acc:
                raise _reject(f"the update expression must not read the "
                              f"accumulator {acc!r} in a conditional "
                              f"update", loop.lineno)
        step_expr = ast.Call(
            func=ast.Name(id=fn_name, ctx=ast.Load()),
            args=[ast.Name(id=acc, ctx=ast.Load()), e_new], keywords=[])
        ast.copy_location(step_expr, e_new)
        ast.fix_missing_locations(step_expr)
    elif isinstance(init_value, ast.List) and not init_value.elts:
        pass          # a list accumulator: its body is append statements
    elif len(body) != 1 or not isinstance(body[0], ast.Assign) \
            or len(body[0].targets) != 1 \
            or not isinstance(body[0].targets[0], ast.Name) \
            or body[0].targets[0].id != acc:
        raise _reject(f"the loop body must be a single assignment to the "
                      f"accumulator {acc!r} in this slice", loop.lineno)
    if step_expr is None and not (isinstance(init_value, ast.List)
                                  and not init_value.elts):
        step_expr = body[0].value
    if index == acc:
        raise _reject("the loop index cannot be the accumulator",
                      loop.lineno)
    if ret_stmt.value is None:
        raise _reject("bare `return` has no value to encode",
                      ret_stmt.lineno)
    for node in ast.walk(ret_stmt.value):
        if isinstance(node, ast.Name) and node.id == index:
            raise _reject(f"the return expression must not read the loop "
                          f"index {index!r} (its post-loop value is a "
                          f"CPython artifact this slice does not model)",
                          ret_stmt.lineno)
    inv_expr, inv_line = _loop_invariants(spec_fn, loop)
    # A True/False initializer marks the BOOL accumulator shape (slice
    # 3): step must be `acc and P` / `acc or P`, return the bare
    # accumulator. The pairing with the annotated return type is
    # checked by the caller, which knows it.
    # A `[]` initializer marks the LIST accumulator shape: the body
    # appends, and `out.append(v)` is `out ++ [v]` because Python
    # appends at the END. The accumulator is a fresh local, so the
    # aliasing question the Dafny backend's ownership rules answer does
    # not arise here — nothing else can hold a reference to it.
    acc_list = isinstance(init_value, ast.List) and not init_value.elts
    if acc_list:
        appended: list[ast.expr] = []
        for st in loop.body:
            if not (isinstance(st, ast.Expr)
                    and isinstance(st.value, ast.Call)
                    and isinstance(st.value.func, ast.Attribute)
                    and st.value.func.attr == "append"
                    and isinstance(st.value.func.value, ast.Name)
                    and st.value.func.value.id == acc
                    and len(st.value.args) == 1
                    and not st.value.keywords):
                raise _reject(
                    f"a list accumulator's body is `{acc}.append(<expr>)` "
                    f"statements in this slice", getattr(st, "lineno",
                                                         loop.lineno))
            appended.append(st.value.args[0])
        if not appended:
            raise _reject("the loop body must append at least once",
                          loop.lineno)
        for a in appended:
            for node in ast.walk(a):
                if isinstance(node, ast.Name) and node.id == acc:
                    raise _reject(
                        f"an appended value must not read the "
                        f"accumulator {acc!r} in this slice", loop.lineno)
        if not (isinstance(ret_stmt.value, ast.Name)
                and ret_stmt.value.id == acc):
            raise _reject("a list-building loop returns the bare "
                          "accumulator in this slice", ret_stmt.lineno)
        step_expr = ast.Tuple(elts=appended)      # carried, not evaluated
        ast.copy_location(step_expr, loop)
        ast.fix_missing_locations(step_expr)
    acc_bool = isinstance(init_value, ast.Constant) \
        and isinstance(init_value.value, bool)
    if acc_bool:
        if not (isinstance(step_expr, ast.BoolOp)
                and len(step_expr.values) == 2
                and isinstance(step_expr.values[0], ast.Name)
                and step_expr.values[0].id == acc):
            raise _reject(
                f"a bool accumulator updates as `{acc} = {acc} and <pred>`"
                f" or `{acc} = {acc} or <pred>` in this slice", loop.lineno)
        for node in ast.walk(step_expr.values[1]):
            if isinstance(node, ast.Name) and node.id == acc:
                raise _reject(f"the accumulator {acc!r} appears only as "
                              f"the left operand of its own update",
                              loop.lineno)
        if not (isinstance(ret_stmt.value, ast.Name)
                and ret_stmt.value.id == acc):
            raise _reject("a bool loop returns the bare accumulator in "
                          "this slice", ret_stmt.lineno)
    return _LoopShape(index=index, acc=acc, init=init_value,
                      acc_list=acc_list,
                      bound=it.args[0], step=step_expr,
                      ret=ret_stmt.value, inv=inv_expr, inv_line=inv_line,
                      for_line=loop.lineno, acc_bool=acc_bool)


def encode_module_lean(source: str, specs: ModuleSpecs, module_name: str,
                       proof_lemmas: frozenset[str] = frozenset()
                       ) -> LeanEncoded:
    if specs.errors:
        first = specs.errors[0]
        raise EncodeError(f"spec error: {first.error}", first.line)
    # Proof sidecars are live (P3). `proof_lemmas` is the set of names
    # the pack declares, already whitelist-validated by the loader.
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
                      "len", "sum", "bool", "result"):
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
        for clause in spec_fn.by_kind("proof"):
            text = clause.desugared if clause.desugared is not None \
                else clause.raw
            try:
                call = ast.parse(text, mode="eval").body
            except SyntaxError as exc:
                raise _reject(f"cannot parse proof clause: {exc.msg}",
                              clause.line)
            if not (isinstance(call, ast.Call)
                    and isinstance(call.func, ast.Name)):
                raise _reject("a `#@ proof` clause names a lemma and its "
                              "arguments, as `Lemma(a, b)`", clause.line)
            if call.func.id not in proof_lemmas:
                raise _reject(
                    f"unknown lemma {call.func.id!r} — a `#@ proof` "
                    f"target must be declared in the sidecar "
                    f"(<stem>.proofs.lean); this one declares "
                    f"{sorted(proof_lemmas) or 'nothing'}", clause.line)
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
        ptypes: dict[str, str] = {}
        for arg in a.args:
            ann = arg.annotation
            if isinstance(ann, ast.Name) and ann.id == "int":
                ptypes[arg.arg] = "Int"
            elif isinstance(ann, ast.Subscript) \
                    and isinstance(ann.value, ast.Name) \
                    and ann.value.id == "list" \
                    and isinstance(ann.slice, ast.Name) \
                    and ann.slice.id == "int":
                ptypes[arg.arg] = "List Int"
            elif isinstance(ann, ast.Subscript) \
                    and isinstance(ann.value, ast.Name) \
                    and ann.value.id in ("tuple", "Tuple"):
                raise _reject(
                    "tuple types are outside the Lean slice — the Dafny "
                    "backend admits them; this slice has no product types",
                    fn.lineno)
            else:
                raise _reject(f"parameter {arg.arg!r} must be `int` or "
                              f"`list[int]` in this slice", fn.lineno)
            # No module-wide check for parameters: a binder shadowing a
            # top-level name is legal Lean (and matches Python scoping).
            # The one genuine capture — a parameter named after its OWN
            # function, which the theorem statement must reference beside
            # it — is alpha-renamed in theorem context below.
        lists0 = frozenset(p for p, t in ptypes.items()
                           if t == "List Int")
        lc0 = _ListCtx(lists0, {}, None,
                       min_len=_requires_min_len(spec_fn, lists0),
                       pos_names=_requires_positive(spec_fn),
                       nonneg_names=_requires_nonneg(spec_fn))
        ret = fn.returns
        if isinstance(ret, ast.Subscript) \
                and isinstance(ret.value, ast.Name) \
                and ret.value.id in ("tuple", "Tuple"):
            raise _reject(
                "tuple types are outside the Lean slice — the Dafny "
                "backend admits them; this slice has no product types",
                fn.lineno)
        is_list_ret = (isinstance(ret, ast.Subscript)
                       and isinstance(ret.value, ast.Name)
                       and ret.value.id == "list"
                       and isinstance(ret.slice, ast.Name)
                       and ret.slice.id == "int")
        if not is_list_ret and not (isinstance(ret, ast.Name)
                                    and ret.id in ("int", "bool")):
            raise _reject("return type must be `int`, `bool`, or "
                          "`list[int]` in this slice", fn.lineno)
        is_bool = (not is_list_ret) and ret.id == "bool"
        if is_list_ret:
            lc0 = _ListCtx(lc0.lists, lc0.safe_idx, lc0.take_idx,
                           lc0.scaffold, lc0.min_len, lc0.pos_names,
                           lc0.result_list, True)
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
            if isinstance(node, ast.Call):
                func = node.func
                if isinstance(func, ast.Name) and func.id in _MATH_FNS:
                    raise _reject(_MATH_LEAN, node.lineno)
                if isinstance(func, ast.Attribute) and func.attr in _MATH_FNS:
                    raise _reject(_MATH_LEAN, node.lineno)
            if isinstance(node, ast.Call) \
                    and isinstance(node.func, ast.Name) \
                    and node.func.id in assigned_anywhere:
                raise _reject(
                    f"call to {node.func.id!r}, which is assigned later "
                    f"in this function — Python treats it as local "
                    f"throughout (UnboundLocalError here), so the call "
                    f"cannot mean the builtin", node.lineno)
            if isinstance(node, (ast.Break, ast.Continue)):
                raise _reject(
                    "break/continue are outside the Lean slice — the "
                    "Dafny backend admits them; this slice's fuel "
                    "recursion has no continue that still advances the "
                    "index", node.lineno)
            if isinstance(node, ast.Return) \
                    and isinstance(node.value, ast.Tuple):
                raise _reject(
                    "tuple literals are outside the Lean slice — the "
                    "Dafny backend admits them; this slice has no "
                    "product types", node.lineno)
            if isinstance(node, ast.Assert):
                raise _reject(
                    "assert is outside the Lean slice — the Dafny "
                    "backend admits it as a VC; this slice has no "
                    "proof-hint statements", node.lineno)
            if isinstance(node, ast.NamedExpr):
                raise _reject(
                    "walrus is outside the Lean slice — the Dafny "
                    "backend admits always-evaluated `:=` as an "
                    "assignment then the bound name; this slice has no "
                    "expression-level assignment", node.lineno)
            if isinstance(node, ast.JoinedStr):
                raise _reject(
                    "f-strings are outside the Lean slice — the Dafny "
                    "backend admits them as concatenation of str "
                    "pieces; this slice has no strings", node.lineno)
            if isinstance(node, ast.Call) \
                    and isinstance(node.func, ast.Name) \
                    and node.func.id in ("str", "int"):
                raise _reject(
                    "str(int)/int(str) are outside the Lean slice — the "
                    "Dafny backend admits them with parse VCs; this "
                    "slice has no strings", node.lineno)
            if isinstance(node, ast.Call) \
                    and isinstance(node.func, ast.Name) \
                    and node.func.id == "sorted":
                raise _reject(
                    "sorted is outside the Lean slice — the Dafny "
                    "backend admits list[int] sorted as PySorted "
                    "(permutation + order); this slice has no "
                    "sequence-sort prelude", node.lineno)
            if isinstance(node, ast.Call) \
                    and isinstance(node.func, ast.Attribute) \
                    and node.func.attr in _DAFNY_STR_METHODS:
                raise _reject(
                    "str methods are outside the Lean slice — the Dafny "
                    "backend admits join/split/find/startswith/"
                    "endswith/replace/strip; this slice has no strings",
                    node.lineno)
        # The same question in SPEC clauses, which are comments and so
        # are invisible to the walk above. A clause calling a name the
        # function also binds as a local is ambiguous — the builtin at
        # spec scope, that binding inside the function — and the
        # encoder refuses ambiguity rather than picking a reading.
        for kind in ("requires", "ensures", "invariant", "decreases"):
            for clause in spec_fn.by_kind(kind):
                text = clause.desugared if clause.desugared is not None \
                    else clause.raw
                try:
                    tree = ast.parse(text, mode="eval").body
                except SyntaxError:
                    continue        # reported precisely elsewhere
                for node in ast.walk(tree):
                    if isinstance(node, ast.JoinedStr):
                        raise _reject(
                            "f-strings are outside the Lean slice — the "
                            "Dafny backend admits them as concatenation "
                            "of str pieces; this slice has no strings",
                            clause.line)
                    if isinstance(node, ast.Call):
                        func = node.func
                        if isinstance(func, ast.Name) and func.id in _MATH_FNS:
                            raise _reject(_MATH_LEAN, clause.line)
                        if isinstance(func, ast.Attribute) \
                                and func.attr in _MATH_FNS:
                            raise _reject(_MATH_LEAN, clause.line)
                    if isinstance(node, ast.Call) \
                            and isinstance(node.func, ast.Attribute) \
                            and node.func.attr in _DAFNY_STR_METHODS:
                        raise _reject(
                            "str methods are outside the Lean slice — "
                            "the Dafny backend admits join/split/find/"
                            "startswith/endswith/replace/strip; this "
                            "slice has no strings", clause.line)
                    if isinstance(node, ast.Call) \
                            and isinstance(node.func, ast.Name) \
                            and node.func.id in ("str", "int"):
                        raise _reject(
                            "str(int)/int(str) are outside the Lean "
                            "slice — the Dafny backend admits them with "
                            "parse VCs; this slice has no strings",
                            clause.line)
                    if isinstance(node, ast.Call) \
                            and isinstance(node.func, ast.Name) \
                            and node.func.id == "sorted":
                        raise _reject(
                            "sorted is outside the Lean slice — the "
                            "Dafny backend admits list[int] sorted as "
                            "PySorted (permutation + order); this slice "
                            "has no sequence-sort prelude",
                            clause.line)
                    if isinstance(node, ast.Call) \
                            and isinstance(node.func, ast.Name) \
                            and node.func.id in assigned_anywhere:
                        raise _reject(
                            f"the {kind} clause calls {node.func.id!r}, "
                            f"which this function also binds as a local "
                            f"— the call is ambiguous (the builtin at "
                            f"spec scope, that binding inside the "
                            f"function), so it is refused rather than "
                            f"guessed", clause.line)

        binders = " ".join(f"({_ident(p)} : {ptypes[p]})" for p in params)
        loop = _split_loop(fn, spec_fn)
        wloop = None
        if loop is None and any(isinstance(n, ast.While)
                                for n in ast.walk(fn)):
            # _split_while either matches or rejects with its own
            # message, so a `while` never falls through to the
            # "this function has no loop" error below.
            wloop = _split_while(fn, spec_fn)
            if is_bool or is_list_ret:
                raise _reject("`while` functions return `int` in this "
                              "slice (integer measures and "
                              "accumulators)", fn.lineno)
        if loop is None and wloop is None \
                and spec_fn.by_kind("invariant"):
            # No loop claims it, so it would be silently dropped — the
            # Dafny backend's unclaimed-clause error, mirrored.
            raise _reject("`invariant` must sit at the top of a loop "
                          "body, and this function has no loop",
                          spec_fn.by_kind("invariant")[0].line)
        if wloop is None and spec_fn.by_kind("decreases"):
            raise _reject("`decreases` is only meaningful on a `while` "
                          "loop in this slice — a for-range loop's fuel "
                          "is its range bound", 
                          spec_fn.by_kind("decreases")[0].line)
        if loop is not None and is_list_ret != loop.acc_list:
            raise _reject(
                "a loop function's accumulator must match its return "
                "type: a `[]`-initialized accumulator built with "
                "`append` returns `list[int]`, anything else `int` or "
                "`bool`", fn.lineno)
        if loop is not None and not loop.acc_list \
                and is_bool != loop.acc_bool:
            raise _reject(
                "a loop function's accumulator must match its return "
                "type in this slice: True/False-initialized accumulators "
                "return `bool`, integer accumulators return `int`",
                fn.lineno)
        if wloop is not None:
            for nm in wloop.accs:
                if nm in params:
                    raise _reject(f"accumulator {nm!r} shadows a "
                                  f"parameter — outside this slice",
                                  wloop.while_line)
            if len(set(wloop.accs)) != len(wloop.accs):
                raise _reject("duplicate accumulator names",
                              wloop.while_line)
            fname = spec_fn.name
            gen_cond, gen_meas = f"{fname}_cond", f"{fname}_meas"
            gen_inv, gen_loop = f"{fname}_inv", f"{fname}_loop"
            gen_thm = f"{fname}_loop_inv"
            for g in (gen_cond, gen_meas, gen_inv, gen_loop, gen_thm):
                _check_name(g, "generated declaration for", fn.lineno,
                            taken)
                taken.add(g)
            args = " ".join(_ident(pn) for pn in params)
            argsp = (args + " ") if args else ""
            nacc = len(wloop.accs)
            avs = [_ident(a) for a in wloop.accs]
            avlist = " ".join(avs)
            body_names = names | set(wloop.accs)
            used_plain = set(params) | set(wloop.accs)
            fuel = "f"
            while fuel in used_plain:
                fuel += "'"
            kvar = "k"
            while kvar in used_plain or kvar == fuel:
                kvar += "'"
            pvar = "p"
            while pvar in used_plain or pvar in (fuel, kvar):
                pvar += "'"
            # Divisor positivity from LOOP CONTEXT. After substitution
            # every step expression is written in terms of the loop-HEAD
            # accumulator values, so facts holding at the head apply to
            # it. The invariant holds at the head; the condition holds
            # additionally wherever the body runs. A `while y != 0` body
            # under an invariant `y >= 0` therefore has y > 0, which is
            # what makes `x % y` well-formed there.
            inv_nn, inv_nz, inv_pos = _sign_facts(wloop.inv)
            cnd_nn, cnd_nz, cnd_pos = _sign_facts(wloop.cond)
            nn = inv_nn | cnd_nn
            nz = inv_nz | cnd_nz
            body_pos = frozenset(lc0.pos_names | inv_pos | cnd_pos
                                 | (nn & nz))
            # The condition is evaluated BEFORE it is known to hold, so
            # only the INVARIANT's facts are available to it — but all of
            # them, including a positivity that two separate conjuncts
            # establish together (`y >= 0` and `y != 0`). Taking only the
            # directly-positive names here rejected valid loops. The
            # condition's own facts stay out, since using the condition
            # to justify its own well-formedness would be circular. The
            # invariant gets neither (same reason); quantifier bounds
            # still apply there.
            cond_pos = frozenset(lc0.pos_names | inv_pos
                                 | (inv_nn & inv_nz))
            # Non-negativity from loop context too, which an exponent
            # needs: `2 ** i` under an invariant `0 <= i <= n` is fine,
            # and zero is a perfectly good exponent.
            body_nn = frozenset(lc0.nonneg_names | nn | inv_pos | cnd_pos)
            body_lc = _ListCtx(lc0.lists, {}, None, min_len=lc0.min_len,
                               pos_names=body_pos, nonneg_names=body_nn)
            cond_lc = _ListCtx(lc0.lists, {}, None, min_len=lc0.min_len,
                               pos_names=cond_pos,
                               nonneg_names=frozenset(lc0.nonneg_names
                                                      | inv_nn | inv_pos))
            inv_lc = _ListCtx(lc0.lists, {}, None, scaffold=True,
                              min_len=lc0.min_len,
                              pos_names=lc0.pos_names,
                              nonneg_names=frozenset(lc0.nonneg_names
                                                     | inv_nn | inv_pos))
            init_ts = [_int_expr(e, names, fn.lineno, lc=lc0)
                       for e in wloop.inits]
            _reject_undecidable_quantifier(wloop.cond, body_names,
                                           wloop.while_line, lc0)
            cond_t = _prop_expr(wloop.cond, body_names, wloop.while_line,
                                lc=cond_lc)
            meas_t = _int_expr(wloop.meas, body_names, wloop.meas_line,
                               lc=body_lc)
            inv_t = _prop_expr(wloop.inv, body_names, wloop.inv_line,
                               lc=inv_lc)
            # Sequential substitution: each body assignment is rewritten
            # through the updates before it, so a step that reads another
            # accumulator sees its NEW value exactly as CPython does.
            subst: dict[str, ast.expr] = {}
            for group in wloop.steps:
                # Every right-hand side in a group is rewritten against
                # the state BEFORE the group, then all of the group's
                # targets are rebound at once — Python's tuple-assignment
                # semantics, and what makes `x, y = y, x` a real swap.
                current = dict(subst)
                updated = {nm: _SubstExprs(current).visit(
                    copy.deepcopy(rhs)) for nm, rhs in group}
                subst.update(updated)
            step_ts = [
                _int_expr(subst[a], body_names, wloop.while_line,
                          lc=body_lc)
                if a in subst else _ident(a)
                for a in wloop.accs]
            acc_ty = "Int" if nacc == 1 else \
                "(" + " × ".join("Int" for _ in avs) + ")"
            tup = avs[0] if nacc == 1 else "(" + ", ".join(avs) + ")"
            step_tup = step_ts[0] if nacc == 1 \
                else "(" + ", ".join(step_ts) + ")"
            arrows = " ".join("Int →" for _ in avs)
            emit("", None)
            emit(f"def {_ident(gen_cond)} {binders} ({avlist} : Int) : "
                 f"Bool := decide {cond_t}", wloop.while_line)
            emit(f"def {_ident(gen_meas)} {binders} ({avlist} : Int) : "
                 f"Int := {meas_t}", wloop.meas_line)
            emit(f"def {_ident(gen_inv)} {binders} ({avlist} : Int) : "
                 f"Prop := {inv_t}", wloop.inv_line)
            emit("", None)
            emit(f"def {_ident(gen_loop)} {binders} : Nat → {arrows} "
                 f"{acc_ty}", wloop.while_line)
            # Match ARMS are comma-separated, unlike binder lists and
            # `intro`, which are space-separated.
            avpat = ", ".join(avs)
            emit(f"  | 0, {avpat} => {tup}", wloop.while_line)
            emit(f"  | ({fuel} + 1), {avpat} => "
                 f"if {_ident(gen_cond)} {argsp}{avlist} then "
                 f"{_ident(gen_loop)} {argsp}{fuel} "
                 + " ".join(f"({t})" for t in step_ts)
                 + f" else {tup}", wloop.while_line)
            emit("", None)
            # The loop application, read back through projections when
            # the state is a tuple.
            app = f"({_ident(gen_loop)} {argsp}{fuel} {avlist})"
            projs = " ".join(f"{app}{_proj(k, nacc)}"
                             for k in range(nacc))
            emit(f"theorem {_ident(gen_thm)} {binders} : "
                 f"∀ ({fuel} : Nat) ({avlist} : Int),", wloop.inv_line)
            emit(f"    {_ident(gen_inv)} {argsp}{avlist} → "
                 f"{_ident(gen_meas)} {argsp}{avlist} ≤ ({fuel} : Int) →",
                 wloop.inv_line)
            emit(f"    {_ident(gen_inv)} {argsp}{projs} ∧",
                 wloop.inv_line)
            emit(f"      {_ident(gen_cond)} {argsp}{projs} = false := by",
                 wloop.inv_line)
            # Variable-divisor mod bounds, now supplyable inside the
            # induction: the invariant and the condition are unfolded
            # into the context by the simp above, so `0 < y` is provable
            # there even though the theorem carries no `requires`. Each
            # `have` is guarded, so a divisor whose positivity is not
            # provable in a given branch simply contributes nothing
            # rather than breaking the proof.
            # A `#@ proof` clause inside the loop body names a lemma
            # the PRESERVATION step needs, not the main theorem, so the
            # instantiation is emitted here as well. Guarded: an
            # argument this slice cannot translate simply contributes
            # nothing.
            wproof_facts: list[str] = []
            for wpi, wclause in enumerate(spec_fn.by_kind("proof")):
                wtext = wclause.desugared if wclause.desugared is not None \
                    else wclause.raw
                try:
                    wcall = ast.parse(wtext, mode="eval").body
                    wargs = " ".join(
                        "(" + _int_expr(arg, body_names, wclause.line,
                                        lc=body_lc) + ")"
                        for arg in wcall.args)
                except (SyntaxError, EncodeError):
                    continue
                wproof_facts.append(
                    f"      have hwp{wpi} := {wcall.func.id} "
                    f"{wargs}".rstrip())
            wdiv_facts: list[str] = []
            wsites: list[tuple[ast.expr, ast.expr]] = []
            for expr in ([wloop.cond, wloop.meas]
                         + [v for g in wloop.steps for _, v in g]):
                for node in ast.walk(expr):
                    if isinstance(node, ast.BinOp) \
                            and isinstance(node.op, ast.Mod):
                        wsites.append((node.left, node.right))
            for wi, (wn, wd) in enumerate(wsites):
                if isinstance(wd, ast.Constant):
                    continue          # already handled by the bridge
                try:
                    wnt = _int_expr(wn, body_names, wloop.while_line,
                                    lc=body_lc)
                    wdt = _int_expr(wd, body_names, wloop.while_line,
                                    lc=body_lc)
                except EncodeError:
                    continue
                wdiv_facts.append(
                    f"      all_goals (try (have hwlo{wi} := "
                    f"VeriPy.PyMod_nonneg {wnt} {wdt} (by omega)))")
                wdiv_facts.append(
                    f"      all_goals (try (have hwhi{wi} := "
                    f"VeriPy.PyMod_lt {wnt} {wdt} (by omega)))")
            sq_facts: list[str] = []
            for qi, qe in enumerate(_squared_terms([wloop.cond,
                                                    wloop.inv])):
                try:
                    qt = _int_expr(qe, body_names, wloop.while_line,
                                   lc=lc0)
                except EncodeError:
                    continue
                sq_facts.append(f"have hsq{qi} := VeriPy.SqGeSelf {qt}")
            wladder = [*wproof_facts, *wdiv_facts,
                       *(f"      {f}" for f in sq_facts),
                       "      all_goals (try omega)",
                       "      all_goals (try simp_all)",
                       "      all_goals (first | omega | trivial)"]
            emit(f"  intro {fuel}", wloop.inv_line)
            emit(f"  induction {fuel} with", wloop.inv_line)
            emit("  | zero =>", wloop.inv_line)
            emit(f"      intro {avlist} h hm", wloop.inv_line)
            emit(f"      simp only [{_ident(gen_loop)}]", wloop.inv_line)
            emit(f"      simp only [{_ident(gen_inv)}, "
                 f"{_ident(gen_meas)}, {_ident(gen_cond)}, "
                 f"decide_eq_false_iff_not] at *", wloop.inv_line)
            for tl in wladder:
                emit(tl, wloop.inv_line)
            emit(f"  | succ {kvar} ih =>", wloop.inv_line)
            emit(f"      intro {avlist} h hm", wloop.inv_line)
            emit(f"      simp only [{_ident(gen_loop)}]", wloop.inv_line)
            emit(f"      by_cases hc : {_ident(gen_cond)} "
                 f"{argsp}{avlist} = true", wloop.inv_line)
            emit("      · rw [if_pos hc]", wloop.inv_line)
            emit("        refine ih "
                 + " ".join(f"({t})" for t in step_ts) + " ?_ ?_",
                 wloop.inv_line)
            emit(f"        · simp only [{_ident(gen_inv)}, "
                 f"{_ident(gen_cond)}, decide_eq_true_eq] at *",
                 wloop.inv_line)
            for tl in wladder:
                emit("    " + tl, wloop.inv_line)
            emit(f"        · simp only [{_ident(gen_meas)}, "
                 f"{_ident(gen_inv)}, {_ident(gen_cond)}, "
                 f"decide_eq_true_eq] at *", wloop.inv_line)
            for tl in wladder:
                emit("    " + tl, wloop.inv_line)
            emit("      · rw [if_neg hc]", wloop.inv_line)
            emit("        simp only [Bool.not_eq_true] at hc",
                 wloop.inv_line)
            emit("        exact ⟨h, hc⟩", wloop.inv_line)
            emit("", None)
            emit(f"def {_ident(spec_fn.name)} {binders} : Int :=",
                 fn.lineno)
            init_call = (f"{_ident(gen_loop)} {argsp}"
                         f"({_ident(gen_meas)} {argsp}"
                         + " ".join(f"({t})" for t in init_ts)
                         + ").toNat "
                         + " ".join(f"({t})" for t in init_ts))
            if nacc == 1:
                ret_t = _int_expr(wloop.ret, body_names, fn.lineno,
                                  lc=lc0)
                emit(f"  let {avs[0]} := {init_call}; {ret_t}",
                     fn.lineno)
            else:
                emit(f"  let {pvar} := {init_call}", fn.lineno)
                for k, a in enumerate(avs):
                    emit(f"  let {a} := {pvar}{_proj(k, nacc)}",
                         fn.lineno)
                ret_t = _int_expr(wloop.ret, body_names, fn.lineno,
                                  lc=lc0)
                emit(f"  {ret_t}", fn.lineno)

        elif loop is not None:
            for nm, what in ((loop.index, "loop index"),
                             (loop.acc, "accumulator")):
                if nm in params:
                    raise _reject(f"{what} {nm!r} shadows a parameter — "
                                  f"outside this slice", loop.for_line)
            body_names = names | {loop.index, loop.acc}
            fname = spec_fn.name
            gen_loop, gen_inv, gen_thm = (f"{fname}_loop", f"{fname}_inv",
                                          f"{fname}_loop_inv")
            for g in (gen_loop, gen_inv, gen_thm):
                _check_name(g, "generated declaration for", fn.lineno,
                            taken)
                taken.add(g)
            args = " ".join(_ident(p) for p in params)
            argsp = (args + " ") if args else ""
            for expr, ln in ((loop.init, fn.lineno),
                             (loop.bound, loop.for_line),
                             (loop.step, loop.for_line),
                             (loop.ret, fn.lineno)):
                _no_old(expr, ln)
            # A loop over `range(len(L))` makes its index structurally
            # in bounds for L, so the STEP may index L. The invariant
            # additionally gets the index as a `xs[:i]` slice bound —
            # proof scaffolding evaluated at loop heads, where i ≥ 0.
            b = loop.bound
            safe: dict[str, str] = {}
            if isinstance(b, ast.Call) and isinstance(b.func, ast.Name) \
                    and b.func.id == "len" and not b.keywords \
                    and len(b.args) == 1 \
                    and isinstance(b.args[0], ast.Name) \
                    and b.args[0].id in lc0.lists:
                safe[loop.index] = b.args[0].id
            step_lc = _ListCtx(lc0.lists, safe, None,
                               min_len=lc0.min_len,
                               pos_names=lc0.pos_names)
            inv_lc = _ListCtx(lc0.lists, dict(safe), loop.index,
                              scaffold=True, min_len=lc0.min_len,
                              pos_names=lc0.pos_names)
            iv, av = _ident(loop.index), _ident(loop.acc)
            acc_ty = ("List Int" if loop.acc_list
                      else ("Bool" if loop.acc_bool else "Int"))
            if loop.acc_list:
                # The accumulator IS a list, so the invariant may take
                # its length and index it. Registering it in the list
                # set is what makes `len(out)` and `out[k]` mean
                # something; scaffold mode already licenses the index,
                # since an invariant is proof machinery rather than
                # executed code.
                acc_lists = lc0.lists | {loop.acc}
                step_lc = _ListCtx(acc_lists, safe, None,
                                   min_len=lc0.min_len,
                                   pos_names=lc0.pos_names,
                                   nonneg_names=lc0.nonneg_names)
                inv_lc = _ListCtx(acc_lists, dict(safe), loop.index,
                                  scaffold=True, min_len=lc0.min_len,
                                  pos_names=lc0.pos_names,
                                  nonneg_names=lc0.nonneg_names)
            # The generated fuel and induction binders are plain
            # identifiers, and «m» IS m: a user accumulator named m
            # (max_element!) would collide with them. Freshen against
            # every name the emitted terms can mention.
            used_plain = set(params) | {loop.index, loop.acc}
            fuel = "m"
            while fuel in used_plain:
                fuel += "'"
            kvar = "k"
            while kvar in used_plain or kvar == fuel:
                kvar += "'"
            bound_t = _int_expr(loop.bound, names, fn.lineno, lc=lc0)
            if loop.acc_list:
                init_t = "([] : List Int)"
                # `out.append(v)` is `out ++ [v]`: Python appends at the
                # END. Several appends in one body chain in order.
                parts = [_int_expr(a, body_names, loop.for_line,
                                   lc=step_lc)
                         for a in loop.step.elts]
                step_t = av
                for part in parts:
                    step_t = f"({step_t} ++ [{part}])"
                inv_t = _prop_expr(loop.inv, body_names, loop.inv_line,
                                   lc=inv_lc)
            elif loop.acc_bool:
                init_t = "true" if loop.init.value else "false"
                # Step: `acc and P` / `acc or P` — P bridges into Bool
                # via decide, mirroring the loop-free predicate path.
                bool_op = "&&" if isinstance(loop.step.op, ast.And) \
                    else "||"
                _reject_undecidable_quantifier(
                    loop.step.values[1], body_names, loop.for_line,
                    step_lc)
                pred_t = _prop_expr(loop.step.values[1], body_names,
                                    loop.for_line, lc=step_lc)
                step_t = f"({av} {bool_op} (decide {pred_t}))"
                # The invariant mentions the Bool accumulator by name;
                # rewriting it to the reserved `result` rides the SAME
                # pinned bridge as a bool ensures clause
                # ((acc = true) ↔ prop). Capture-free by the checks.
                for node in ast.walk(loop.inv):
                    if isinstance(node, ast.Name) and node.id == "result":
                        raise _reject("`result` is only meaningful in "
                                      "`ensures`", loop.inv_line)
                    if isinstance(node, ast.comprehension) \
                            and isinstance(node.target, ast.Name) \
                            and node.target.id == loop.acc:
                        raise _reject(
                            f"a quantifier binder shadows the "
                            f"accumulator {loop.acc!r} — outside this "
                            f"slice", loop.inv_line)
                inv_sub = _SubstName(loop.acc).visit(loop.inv)
                inv_t = _prop_expr(inv_sub, body_names, loop.inv_line,
                                   result=av, result_is_bool=True,
                                   lc=inv_lc)
            else:
                init_t = _int_expr(loop.init, names, fn.lineno, lc=lc0)
                step_t = _int_expr(loop.step, body_names, loop.for_line,
                                   lc=step_lc)
                inv_t = _prop_expr(loop.inv, body_names, loop.inv_line,
                                   lc=inv_lc)
            emit("", None)
            # Fuel recursion on Nat: structurally terminating, so no
            # termination_by; range(N) with negative N is the empty loop
            # via .toNat clamping, matching CPython.
            emit(f"def {_ident(gen_loop)} {binders} : "
                 f"Nat → Int → {acc_ty} → {acc_ty}", loop.for_line)
            emit(f"  | 0, _, {av} => {av}", loop.for_line)
            emit(f"  | ({fuel} + 1), {iv}, {av} => "
                 f"{_ident(gen_loop)} {argsp}{fuel} ({iv} + 1) {step_t}",
                 loop.for_line)
            emit("", None)
            emit(f"def {_ident(gen_inv)} {binders} "
                 f"({iv} : Int) ({av} : {acc_ty}) : Prop :=",
                 loop.inv_line)
            emit(f"  {inv_t}", loop.inv_line)
            emit("", None)
            # The induction theorem: its inductive step IS the
            # invariant-preservation VC (omega for linear invariants).
            # The loop application is one opaque atom to omega, so the
            # index arithmetic (i+1)+k vs i+(k+1) closes linearly.
            # The fuel-bound hypothesis (i + fuel ≤ N) rides the whole
            # induction: a len-bounded ∃-witness invariant
            # (max_element class) must survive the tail of the fold,
            # where the totalized getD would otherwise smuggle in
            # elements the list does not have. Inert for prefix-only
            # invariants — every discharge is one more omega goal.
            emit(f"theorem {_ident(gen_thm)} {binders} : "
                 f"∀ ({fuel} : Nat) ({iv} : Int) ({av} : {acc_ty}),",
                 loop.inv_line)
            emit(f"    {_ident(gen_inv)} {argsp}{iv} {av} → 0 ≤ {iv} → "
                 f"{iv} + ({fuel} : Int) ≤ {bound_t} →",
                 loop.inv_line)
            emit(f"    {_ident(gen_inv)} {argsp}({iv} + {fuel}) "
                 f"({_ident(gen_loop)} {argsp}{fuel} {iv} {av}) := by",
                 loop.inv_line)
            # The endgame ladder: omega closes linear goals as before;
            # `simp_all` then folds hypotheses into goals list atoms
            # keep out of omega's reach; the guarded `congr` bridge
            # closes `PySum (take A xs) = PySum (take B xs)` residues
            # where A = B is linear but trapped inside the atoms
            # (measured: the succ case leaves exactly that shape,
            # (i+1+k) vs (i+(k+1)) under the take).
            # A list accumulator's invariants talk about `length`, and
            # appending is `++ [v]`. Gated on the list case: firing
            # these on an int loop rewrote goals whose hypotheses kept
            # the old form, which is how the earlier getD lemmas broke
            # max_element.
            list_facts = ([
                "      all_goals (try simp only [List.length_append, "
                "List.length_cons, List.length_nil])",
                "      all_goals (try push_cast)",
            ] if loop.acc_list else [])
            ladder = [*list_facts,
                      "      all_goals (try omega)",
                      "      all_goals (try simp_all)",
                      "      all_goals (try (congr 2 <;> omega))",
                      "      all_goals (first | omega | trivial)"]
            # Division facts for sites INSIDE the loop. Only constant
            # divisors: the induction theorem carries the invariant and
            # the fuel bound, not the function's `requires`, so a
            # variable divisor's positivity is not provable here (that
            # stays honest incompleteness rather than a false proof).
            div_facts: list[str] = []
            for di, (dnum, dden, dis_mod) in enumerate(
                    _divmod_sites(fn, spec_fn)):
                if not (dis_mod and isinstance(dden, ast.Constant)
                        and isinstance(dden.value, int)
                        and dden.value > 0):
                    continue
                try:
                    dn = _int_expr(dnum, body_names, loop.for_line,
                                   lc=step_lc)
                except EncodeError:
                    continue
                div_facts.append(
                    f"      have hlo{di} := VeriPy.PyMod_nonneg "
                    f"{dn} {dden.value} (by omega)")
                div_facts.append(
                    f"      have hhi{di} := VeriPy.PyMod_lt "
                    f"{dn} {dden.value} (by omega)")
            emit(f"  intro {fuel}", loop.inv_line)
            emit(f"  induction {fuel} with", loop.inv_line)
            emit(f"  | zero =>", loop.inv_line)
            emit(f"      intro {iv} {av} h hi hb", loop.inv_line)
            emit(f"      simp only [{_ident(gen_loop)}, {_ident(gen_inv)}]"
                 f" at h ⊢", loop.inv_line)
            for fact in div_facts:
                emit(fact, loop.inv_line)
            emit("      all_goals (try push_cast)", loop.inv_line)
            for step_line in ladder:
                emit(step_line, loop.inv_line)
            emit(f"  | succ {kvar} ih =>", loop.inv_line)
            emit(f"      intro {iv} {av} h hi hb", loop.inv_line)
            emit(f"      simp only [{_ident(gen_loop)}]", loop.inv_line)
            for fact in div_facts:
                emit(fact, loop.inv_line)
            # The inner `by` is the invariant-preservation VC. Linear
            # invariants close on omega alone; take-slice invariants
            # need (i+1).toNat unfolded to i.toNat+1 (sound under hi)
            # so PySum_take_succ can peel the (i+1)-prefix into the
            # i-prefix plus the getD element omega can then match; the
            # Bool shapes get a constructor script that splits the
            # fresh index off the ∀/∃ prefix (below_threshold/contains
            # classes, both live-measured).
            emit(f"      have hstep := ih ({iv} + 1)", loop.inv_line)
            emit(f"        {step_t}", loop.inv_line)
            def _is_quant(e: ast.expr, which: str) -> bool:
                return isinstance(e, ast.Call) \
                    and isinstance(e.func, ast.Name) and e.func.id == which

            quant_pair = None
            if isinstance(loop.inv, ast.BoolOp) \
                    and isinstance(loop.inv.op, ast.And) \
                    and len(loop.inv.values) == 2:
                c1, c2 = loop.inv.values
                if _is_quant(c1, "all") and _is_quant(c2, "any"):
                    quant_pair = "forall_first"
                elif _is_quant(c1, "any") and _is_quant(c2, "all"):
                    quant_pair = "exists_first"
            step_is_maxmin = (isinstance(loop.step, ast.Call)
                              and isinstance(loop.step.func, ast.Name)
                              and loop.step.func.id in ("max", "min")
                              and len(loop.step.args) == 2
                              and isinstance(loop.step.args[0], ast.Name)
                              and loop.step.args[0].id == loop.acc)
            if not loop.acc_bool and quant_pair and step_is_maxmin:
                # The max_element class: a prefix ∀-bound conjoined
                # with a len-bounded ∃-witness, stepped by max/min
                # (omega-native, so no ite splits inside the loop
                # atom). The ∀ bullet splits the fresh index off the
                # prefix; the ∃ bullet keeps the old witness or takes
                # the fresh index, decided by by_cases on the update —
                # the fresh witness is in range by the fuel bound hb.
                e2_t = _int_expr(loop.step.args[1], body_names,
                                 loop.for_line, lc=step_lc)
                # by_cases picks the branch that leaves the OLD value:
                # for max that is E ≤ acc, for min it is acc ≤ E — the
                # true branch keeps the old witness, the false branch
                # takes the fresh index.
                hc_cmp = f"{e2_t} ≤ {av}" \
                    if loop.step.func.id == "max" else f"{av} ≤ {e2_t}"
                forall_bullets = (
                    "             · intro j hj",
                    f"               rcases (by omega : j < {iv} ∨ "
                    f"j = {iv}) with hlt | rfl",
                    "               · have := {H} j ⟨hj.1, hlt⟩; omega",
                    "               · omega",
                )
                exists_bullets = (
                    "             · obtain ⟨w, hw, hwv⟩ := {H}",
                    f"               by_cases hc : {hc_cmp}",
                    "               · exact ⟨w, hw, by omega⟩",
                    f"               · exact ⟨{iv}, ⟨hi, by "
                    f"(try push_cast at hb ⊢); omega⟩, by omega⟩",
                )
                if quant_pair == "forall_first":
                    bullets = [line.replace("{H}", "h1")
                               for line in forall_bullets] \
                            + [line.replace("{H}", "h2")
                               for line in exists_bullets]
                else:
                    bullets = [line.replace("{H}", "h1")
                               for line in exists_bullets] \
                            + [line.replace("{H}", "h2")
                               for line in forall_bullets]
                for tl in (
                    "        (by",
                    f"          simp only [{_ident(gen_inv)}] at h ⊢",
                    "          first",
                    "          | omega",
                    "          | (obtain ⟨h1, h2⟩ := h",
                    "             constructor",
                    *bullets,
                    "             )",
                    "        )",
                ):
                    emit(tl, loop.inv_line)
            elif loop.acc_list:
                # A list accumulator's preservation step is about
                # length and append, not prefix sums, so it gets its own
                # discharge rather than falling through to the PySum
                # rewrite, which cannot match here and errors when it
                # tries.
                for tl in (
                    "        (by",
                    f"          simp only [{_ident(gen_inv)}] at h ⊢",
                    "          all_goals (try simp only "
                    "[List.length_append, List.length_cons, "
                    "List.length_nil])",
                    "          all_goals (try push_cast)",
                    "          all_goals (try omega)",
                    "          all_goals (try simp_all)",
                    "          all_goals (first | omega | trivial))",
                ):
                    emit(tl, loop.inv_line)
            elif not loop.acc_bool:
                emit(f"        (by simp only [{_ident(gen_inv)}] at h ⊢; "
                     f"first | omega | (rw [show ({iv} + 1).toNat = "
                     f"({iv}).toNat + 1 from by omega]; "
                     f"simp only [VeriPy.PySum_take_succ]; omega))",
                     loop.inv_line)
            elif isinstance(loop.step.op, ast.And):
                # The `first | exact ... | omega` leaves bridge the
                # syntactic gap between the invariant body and the step
                # predicate (an early-return loop tests `l[i] >= t`
                # while its invariant states `l[k] < t` — same linear
                # fact, different spelling).
                for tl in (
                    "        (by",
                    f"          simp only [{_ident(gen_inv)}, "
                    f"Bool.and_eq_true, decide_eq_true_eq] at h ⊢",
                    "          first",
                    "          | omega",
                    "          | (constructor",
                    "             · rintro ⟨hb, hlast⟩ j hj",
                    f"               rcases (by omega : j < {iv} ∨ "
                    f"j = {iv}) with hlt | rfl",
                    "               · exact (h.mp hb) j ⟨hj.1, hlt⟩",
                    "               · first | exact hlast | omega",
                    "             · intro hall",
                    "               refine ⟨h.mpr (fun j hj => hall j "
                    "⟨hj.1, by omega⟩), ?_⟩",
                    f"               have hpi := hall {iv} "
                    f"⟨hi, by omega⟩",
                    "               first | exact hpi | omega))",
                ):
                    emit(tl, loop.inv_line)
            else:
                for tl in (
                    "        (by",
                    f"          simp only [{_ident(gen_inv)}, "
                    f"Bool.or_eq_true, decide_eq_true_eq] at h ⊢",
                    "          first",
                    "          | omega",
                    "          | (constructor",
                    "             · rintro (hb | hlast)",
                    "               · obtain ⟨j, hj, hpj⟩ := h.mp hb",
                    "                 exact ⟨j, ⟨hj.1, by omega⟩, hpj⟩",
                    f"               · refine ⟨{iv}, ⟨hi, by omega⟩, "
                    f"?_⟩",
                    "                 first | exact hlast | omega",
                    "             · rintro ⟨j, hj, hpj⟩",
                    f"               rcases (by omega : j < {iv} ∨ "
                    f"j = {iv}) with hlt | rfl",
                    "               · exact Or.inl (h.mpr ⟨j, "
                    "⟨hj.1, hlt⟩, hpj⟩)",
                    "               · refine Or.inr ?_",
                    "                 first | exact hpj | omega))",
                ):
                    emit(tl, loop.inv_line)
            emit("        (by omega)", loop.inv_line)
            emit("        (by (try push_cast at hb ⊢); omega)",
                 loop.inv_line)
            emit(f"      simp only [{_ident(gen_inv)}] at hstep ⊢",
                 loop.inv_line)
            emit("      all_goals (try push_cast at hstep ⊢)",
                 loop.inv_line)
            # Shape-independent transport: after the index rewrite
            # ((i+1)+k = i+(k+1), sound by omega), hstep IS the goal —
            # this closes iff-of-quantifier invariants the arithmetic
            # ladder cannot touch, and short-circuits the linear ones.
            emit(f"      all_goals (try (rw [show ({iv} + 1 + "
                 f"({kvar} : Int)) = ({iv} + (({kvar} : Int) + 1)) "
                 f"from by omega] at hstep))", loop.inv_line)
            emit("      all_goals (try (exact hstep))", loop.inv_line)
            for step_line in ladder:
                emit(step_line, loop.inv_line)
            ret_t = av if (loop.acc_bool or loop.acc_list) \
                else _int_expr(loop.ret, names | {loop.acc}, fn.lineno,
                               lc=lc0)
            emit("", None)
            emit(f"def {_ident(spec_fn.name)} {binders} : {acc_ty} :=",
                 fn.lineno)
            emit(f"  let {av} := {_ident(gen_loop)} {argsp}"
                 f"({bound_t}).toNat 0 {init_t}; {ret_t}", fn.lineno)
        else:
            body = _body_expr([s for s in fn.body
                               if not (isinstance(s, ast.Expr)
                                       and isinstance(s.value, ast.Constant))],
                              names, params, is_bool, lc0,
                              is_list=is_list_ret)
            ret_ty = ("List Int" if is_list_ret
                      else ("Bool" if is_bool else "Int"))
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

        thm_binders = " ".join(f"({_ident(_tname(p))} : {ptypes[p]})"
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
                f"{_prop_expr(expr, names, line, rename=rename, avoid=avoid, lc=lc0)})")
        # Dafny's clause-ordering rule: an `ensures` may lean on the
        # clauses BEFORE it for well-formedness, because those are
        # proven first. `ensures result >= 1` therefore licenses a later
        # `a % result`. Not circular — clause 1 is checked with no
        # assumptions, and each later clause only assumes what is
        # already established.
        posts = []
        earlier_posts: list[str] = []
        post_lc = lc0
        for expr, line in ensures:
            posts.append((_prop_expr(expr, names, line, result=app,
                                     rename=rename,
                                     result_is_bool=is_bool,
                                     avoid=avoid, lc=post_lc), line))
            lmatch = (_result_length_match(expr, lc0.lists)
                      if is_list_ret else None)
            if lmatch is not None and post_lc.result_list is None:
                post_lc = _ListCtx(post_lc.lists, post_lc.safe_idx,
                                   post_lc.take_idx, post_lc.scaffold,
                                   post_lc.min_len, post_lc.pos_names,
                                   lmatch, post_lc.result_is_list)
            _, _, e_pos = _sign_facts(expr)
            if e_pos:
                # Remember the TRANSLATED clause: if a later divisor
                # rests on it, the generated proof has to establish it
                # first, because it is part of the goal rather than a
                # hypothesis.
                earlier_posts.append(posts[-1][0])
                post_lc = _ListCtx(post_lc.lists, post_lc.safe_idx,
                                   post_lc.take_idx, post_lc.scaffold,
                                   post_lc.min_len,
                                   frozenset(post_lc.pos_names | e_pos),
                                   post_lc.result_list,
                                   post_lc.result_is_list)
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
        if wloop is not None:
            targs = " ".join(_ident(_tname(pn)) for pn in params)
            targsp = (targs + " ") if targs else ""
            w_inits = " ".join(
                "(" + _int_expr(e, names, fn.lineno, rename=rename,
                                lc=lc0) + ")"
                for e in wloop.inits)
            gi, gm = f"{spec_fn.name}_inv", f"{spec_fn.name}_meas"
            gc, gt = f"{spec_fn.name}_cond", f"{spec_fn.name}_loop_inv"
            emit("  try dsimp only", first_ensures_line)
            emit(f"  have hi0 : {_ident(gi)} {targsp}{w_inits} := by "
                 f"simp only [{_ident(gi)}]; all_goals (try push_cast); "
                 f"all_goals (try omega); all_goals (try simp_all); "
                 f"all_goals (try intros); "
                 f"all_goals (first | omega | trivial)",
                 first_ensures_line)
            # The fuel is the measure at entry, so the fuel-bound
            # obligation is exactly "the measure starts non-negative".
            emit(f"  have hfin := {_ident(gt)} {targsp}"
                 f"({_ident(gm)} {targsp}{w_inits}).toNat {w_inits} hi0 "
                 f"(by simp only [{_ident(gm)}]; omega)",
                 first_ensures_line)
            emit("  obtain ⟨hinv, hcond⟩ := hfin", first_ensures_line)
            emit(f"  simp only [{_ident(gi)}, {_ident(gc)}, "
                 f"decide_eq_false_iff_not] at hinv hcond",
                 first_ensures_line)
        elif loop is not None:
            # Bring the invariant through the loop: instantiate the
            # induction theorem at (fuel = bound.toNat, i = 0,
            # acc = init), then rewrite the fuel cast back to the bound
            # (needs bound ≥ 0 provable from the requires — a negative
            # bound is still a CORRECT empty loop in the def, but this
            # generated proof does not cover it). Terms are translated
            # in THEOREM context (renamed binders) so they match the
            # unfolded goal syntactically; the loop application is then
            # one shared atom for omega.
            targs = " ".join(_ident(_tname(p)) for p in params)
            targsp = (targs + " ") if targs else ""
            if loop.acc_list:
                t_init = "([] : List Int)"
            elif loop.acc_bool:
                t_init = "true" if loop.init.value else "false"
            else:
                t_init = _int_expr(loop.init, names, fn.lineno,
                                   rename=rename, lc=lc0)
            t_bound = _int_expr(loop.bound, names, fn.lineno,
                                rename=rename, lc=lc0)
            emit("  try dsimp only", first_ensures_line)
            # hi0's simp_all carries PySum's equation lemmas: the
            # invariant at entry typically needs `PySum (take 0) = 0`
            # (take_zero, then the nil equation) — inert for loop-free
            # integer invariants, where omega has already closed.
            init_lit_idx = (isinstance(loop.init, ast.Subscript)
                            and isinstance(loop.init.value, ast.Name)
                            and isinstance(loop.init.slice, ast.Constant))
            if not loop.acc_bool and quant_pair and init_lit_idx:
                # The ∃-witness conjunct needs an entry witness the
                # ladder cannot invent: the literal init index itself
                # (`m = l[0]` seeds the witness 0; its bound holds by
                # the requires clause that licensed the literal).
                c = loop.init.slice.value
                fa = ("  · intro j hj", "    omega")
                ex = (f"  · exact ⟨{c}, ⟨by omega, by omega⟩, "
                      f"by first | rfl | simp | omega⟩",)
                b = fa + ex if quant_pair == "forall_first" else ex + fa
                for tl in (f"  have hi0 : "
                           f"{_ident(f'{spec_fn.name}_inv')} "
                           f"{targsp}0 {t_init} := by",
                           f"    simp only "
                           f"[{_ident(f'{spec_fn.name}_inv')}]",
                           "    constructor",
                           *("  " + x for x in b)):
                    emit(tl, first_ensures_line)
            else:
                emit(f"  have hi0 : {_ident(f'{spec_fn.name}_inv')} "
                     f"{targsp}0 {t_init} := by "
                     f"simp only [{_ident(f'{spec_fn.name}_inv')}]; "
                     f"all_goals (try push_cast); all_goals (try omega); "
                     f"all_goals (try simp_all [VeriPy.PySum]); "
                     f"all_goals (try intros); "
                     f"all_goals (first | omega | trivial)",
                     first_ensures_line)
            emit(f"  have hfin := {_ident(f'{spec_fn.name}_loop_inv')} "
                 f"{targsp}({t_bound}).toNat 0 {t_init} hi0 (by omega) "
                 f"(by omega)",
                 first_ensures_line)
            emit(f"  simp only [{_ident(f'{spec_fn.name}_inv')}] at hfin",
                 first_ensures_line)
            # Guarded like every other generated step: an invariant
            # that never mentions the loop index leaves no `↑bound.toNat`
            # in hfin once the invariant is unfolded, and an unguarded
            # `rw` then fails the whole proof (measured: a true spec
            # whose invariant was index-free failed as postcondition).
            emit(f"  all_goals (try rw [Int.toNat_of_nonneg "
                 f"(by omega : (0:Int) ≤ {t_bound})] at hfin)",
                 first_ensures_line)
            # For a `range(len(xs))` loop the invariant lands at
            # `take (0 + ↑xs.length).toNat`: normalize the casts and
            # collapse `take xs.length` to the whole list so hfin's
            # atoms match the ensures translation (`PySum xs`). Inert
            # (hence `try`) when no list is involved.
            emit("  all_goals (try simp only [Int.toNat_natCast, "
                 "Int.zero_add, List.take_length] at hfin)",
                 first_ensures_line)
            # After normalization hfin often IS the ensures goal
            # (measured on the contains class, whose ∃-postcondition no
            # fixed script could otherwise witness — the invariant
            # induction carries the witness through the loop).
            emit("  all_goals (try (exact hfin))", first_ensures_line)
        # Division sites: supply the positivity fact each one's
        # well-formedness rests on, the mod bounds omega cannot derive for
        # a VARIABLE divisor, and the bridges to Lean's own `/` and `%`
        # (which omega does reason about natively, for constant divisors).
        seen_div: dict[str, str] = {}
        emitted_earlier = False
        for si, (num, den, is_mod) in enumerate(_divmod_sites(fn, spec_fn)):
            try:
                # Same context the ACCEPTANCE used, `result` included:
                # translating the divisor without it silently skipped
                # every site whose positivity came from an earlier
                # clause, so a contract the encoder had just admitted
                # went to the prover with no bounds at all.
                den_t = _int_expr(den, names, first_ensures_line,
                                  result=app, rename=rename, lc=post_lc)
                num_t = _int_expr(num, names, first_ensures_line,
                                  result=app, rename=rename, lc=post_lc)
            except EncodeError:
                # The site reads a name bound INSIDE the loop (the index
                # or the accumulator), which theorem context does not
                # bind. Skipping costs proof hints, never safety: the
                # divisor obligation is enforced where the expression is
                # actually translated, under the loop's own context.
                continue
            hname = seen_div.get(den_t)
            if hname is None:
                hname = f"hdpos{len(seen_div)}"
                seen_div[den_t] = hname
                if app in den_t and earlier_posts and not emitted_earlier:
                    # The divisor mentions `result`, so its positivity
                    # rests on an earlier clause — which is a GOAL
                    # conjunct, not a hypothesis. Prove it up front so
                    # omega can use it.
                    for ei, ep in enumerate(earlier_posts):
                        emit(f"  have hpost{ei} : {ep} := by",
                             first_ensures_line)
                        for tl in ("    try unfold VeriPy.PyAbs",
                                   "    try dsimp only",
                                   "    try simp only [decide_eq_true_eq]",
                                   "    repeat' split",
                                   "    all_goals (try intros)",
                                   "    all_goals (try simp_all)",
                                   "    all_goals (first | omega | trivial)"):
                            emit(tl, first_ensures_line)
                    emitted_earlier = True
                emit(f"  have {hname} : (0:Int) < {den_t} := by omega",
                     first_ensures_line)
            if is_mod:
                emit(f"  have hdlo{si} := VeriPy.PyMod_nonneg "
                     f"{num_t} {den_t} {hname}", first_ensures_line)
                emit(f"  have hdhi{si} := VeriPy.PyMod_lt "
                     f"{num_t} {den_t} {hname}", first_ensures_line)
            # Bridge ONLY for a constant divisor. omega reasons about
            # `%` and `/` natively there, so the rewrite unlocks real
            # arithmetic. For a VARIABLE divisor omega treats `a % p` as
            # an opaque atom either way (measured), and rewriting the
            # goal while the bound hypotheses stay in PyMod form splits
            # one atom into two unrelated ones — which is exactly how
            # this first failed.
            if isinstance(den, ast.Constant):
                bridge = "PyMod_pos" if is_mod else "PyFloorDiv_pos"
                emit(f"  all_goals (try rw [VeriPy.{bridge} {num_t} "
                     f"{den_t} {hname}])", first_ensures_line)
        # A `#@ proof` clause instantiates a pack lemma at the
        # arguments the author chose. Emitting it as a `have` puts the
        # fact in context for the same fixed script that proves
        # everything else, rather than inventing a bespoke tactic per
        # task.
        for pi, clause in enumerate(spec_fn.by_kind("proof")):
            text = clause.desugared if clause.desugared is not None \
                else clause.raw
            call = ast.parse(text, mode="eval").body
            try:
                pargs = " ".join(
                    "(" + _int_expr(arg, names, clause.line, result=app,
                                    rename=rename, lc=lc0) + ")"
                    for arg in call.args)
            except EncodeError:
                # An argument this slice cannot translate (a list, a
                # comprehension) is not a reason to fail the whole
                # module: the lemma simply goes uninstantiated and the
                # proof stands or falls without it.
                continue
            emit(f"  have hproof{pi} := {call.func.id} {pargs}".rstrip(),
                 clause.line)
        # Prelude definitions are opaque to omega — a goal containing
        # VeriPy.PyAbs is unprovable until it unfolds to its
        # if-then-else (measured: every abs()-using module failed as
        # postcondition, shadowed or not — no earlier live case called
        # abs). `try`, because unfold fails when the constant does not
        # occur.
        emit("  try unfold VeriPy.PyAbs", first_ensures_line)
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
        # List goals: `map` preserves length and commutes with
        # indexing, and the index bound the quantifier supplies is what
        # turns `getElem?` into `getElem`. Inert when no list is
        # involved, hence guarded.
        # ONLY for list-returning functions. These rewrites turn
        # `getD` into `getElem?`, and firing them on an int-returning
        # list task rewrote the goal while a hypothesis kept the old
        # form — one atom split into two, and a loop proof that had
        # been passing broke. Nothing outside this branch sees them.
        if is_list_ret:
            emit("  all_goals (try simp only "
                 "[List.getD_eq_getElem?_getD, List.getElem?_map, "
                 "List.length_map])", first_ensures_line)
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
        if is_list_ret:
            emit("  all_goals (try (rw [List.getElem?_eq_getElem "
                 "(by omega : _ < _)]))", first_ensures_line)
        emit("  all_goals (try simp_all)", first_ensures_line)
        # Products of equal factors: a goal like `(i - 1) * i = n * (n +
        # 1)` under `i = n + 1` is opaque to omega, which sees two
        # unrelated atoms, but splitting the product first leaves two
        # linear equations. The loop ladder already carries this bridge;
        # the main theorem needs it wherever a lemma pack lands a
        # product in the goal.
        emit("  all_goals (try (congr 1 <;> omega))", first_ensures_line)
        emit("  all_goals (first | omega | trivial)", first_ensures_line)

    # Ask Lean for every proved theorem's axiom footprint. The driver
    # then refuses anything outside the allowed set — the SEMANTIC
    # no-assumption guarantee a syntactic whitelist can only
    # approximate, since a whitelist must enumerate the ways a proof
    # might cheat while the footprint reports what it actually used.
    if theorems:
        lines.append("")
        for t in theorems:
            lines.append(f"#print axioms {_ident(t)}")
    return LeanEncoded(lean_source="\n".join(lines) + "\n",
                       line_map=line_map, theorems=theorems)
