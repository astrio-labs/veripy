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
from dataclasses import dataclass, field

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
        if isinstance(idx, ast.Name) \
                and lc.safe_idx.get(idx.id) == "@result":
            # Licensed by the binder's own bound: the quantifier
            # ranges over `range(len(result))`, so the read never
            # leaves the list (the intersperse class). An UNBOUNDED
            # result read stays rejected below -- totalizing it would
            # let a spec Dafny refuses hold vacuously here.
            return (f"({result}.getD "
                    f"({_lref(idx.id, rename)}).toNat 0)")
        if lc.scaffold:
            # Same story as the param-list scaffold fallback below,
            # extended to `result` now that the WF pre-pass appends
            # an in-bounds obligation for every read no structural
            # rule licensed: the totalized getD is paired with a
            # goal conjunct Dafny-style, so `result[i + 1]` under a
            # binder over `range(len(result) - 1)` (the sorted-unique
            # adjacency spec) is admitted and its bound is PROVED,
            # while an unbounded read makes the theorem unprovable
            # instead of quietly true.
            it_ = _int_expr(idx, names, line, result, rename, lc)
            return f"({result}.getD ({it_}).toNat 0)"
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
        if isinstance(idx, ast.UnaryOp) \
                and isinstance(idx.op, ast.USub) \
                and isinstance(idx.operand, ast.Constant) \
                and idx.operand.value == 1 \
                and (lc.min_len or {}).get(e.value.id, 0) >= 1:
            # `xs[-1]` is the LAST element, licensed by a nonemptiness
            # the context already holds (a requires length bound, or
            # the fall-through of an `if not xs: return` guard) --
            # Python raises on the empty list, so without that bound
            # the totalized read would model a program that crashes.
            base = _lref(e.value.id, rename)
            return (f"({base}.getD ((({base}.length : Int)) - 1)"
                    f".toNat 0)")
        if isinstance(idx, ast.BinOp) and isinstance(idx.op, ast.Sub) \
                and isinstance(idx.right, ast.Name) \
                and lc.safe_for(idx.right.id, e.value.id) \
                and isinstance(idx.left, ast.BinOp) \
                and isinstance(idx.left.op, ast.Sub) \
                and isinstance(idx.left.right, ast.Constant) \
                and idx.left.right.value == 1 \
                and isinstance(idx.left.left, ast.Call) \
                and isinstance(idx.left.left.func, ast.Name) \
                and idx.left.left.func.id == "len" \
                and len(idx.left.left.args) == 1 \
                and isinstance(idx.left.left.args[0], ast.Name) \
                and idx.left.left.args[0].id == e.value.id:
            # MIRROR closure: `xs[len(xs) - 1 - i]` with i already
            # safe for xs — 0 ≤ i < len forces 0 ≤ len-1-i < len, so
            # the read is in bounds by the same construction that
            # licensed i (the palindrome class reads both ends of
            # the same window).
            base = _lref(e.value.id, rename)
            i_ = _lref(idx.right.id, rename)
            return (f"({base}.getD (({base}.length : Int) - 1 - "
                    f"{i_}).toNat 0)")
        if lc.scaffold:
            # SCAFFOLD positions (invariants, spec clauses) are proof
            # machinery, never executed: the totalized getD needs no
            # well-formedness story, and the invariant's own bounds
            # carry the meaning (the intersperse class reads
            # `numbers[k // 2]` under `k < len(out)`). Executable
            # positions keep the structural check below.
            it = _int_expr(idx, names, line, result, rename, lc)
            return (f"({_lref(e.value.id, rename)}.getD "
                    f"({it}).toNat 0)")
        raise _reject(
            f"index into {e.value.id!r} is not structurally in bounds — "
            f"this slice indexes a list only by the loop index of `for i "
            f"in range(len({e.value.id}))`, a quantifier binder over "
            f"`range(len({e.value.id}))`, or a literal below a "
            f"requires-clause length bound", line)
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute) \
            and e.func.attr == "count" and len(e.args) == 1 \
            and not e.keywords \
            and isinstance(e.func.value, ast.Name) \
            and (e.func.value.id in lc.lists
                 or (e.func.value.id == "result" and result is not None
                     and lc.result_is_list)):
        # `xs.count(v)` is List.count — a Nat, cast to Int so it lives
        # in the one arithmetic world the fragment models (Python's
        # count is a plain int). The filtered-comprehension class
        # states its multiplicity posts with this.
        base = (result if e.func.value.id == "result"
                else _lref(e.func.value.id, rename))
        a = _int_expr(e.args[0], names, line, result, rename, lc)
        return f"(({base}.count {a} : Nat) : Int)"
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
        if e.func.id == "len" and len(args) == 1 \
                and isinstance(args[0], ast.Name) \
                and args[0].id == "result" and result is not None \
                and lc.result_is_list:
            return f"(({result}.length : Int))"
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
            if isinstance(a0, ast.GeneratorExp):
                # `sum(f(x) for x in ITER)` folds a MAPPED list:
                # PySum ∘ map. The iterable reuses the same two forms
                # the plain-sum branch admits (a list parameter, or its
                # loop-index prefix), so the take/map order is fixed as
                # map-outside-take -- the order Map_take_succ states.
                if len(a0.generators) == 1 \
                        and not a0.generators[0].ifs \
                        and not a0.generators[0].is_async \
                        and isinstance(a0.generators[0].target, ast.Name):
                    gv = a0.generators[0].target.id
                    if gv in names:
                        raise _reject(
                            f"generator binder {gv!r} shadows a name in "
                            f"scope — outside this slice", line)
                    gbody = _int_expr(a0.elt, names | {gv}, line,
                                      rename=rename, lc=lc)
                    gfn = f"(fun {_ident(gv)} => {gbody})"
                    git = a0.generators[0].iter
                    if isinstance(git, ast.Name) and git.id in lc.lists:
                        return (f"(VeriPy.PySum "
                                f"({_lref(git.id, rename)}.map {gfn}))")
                    if isinstance(git, ast.Subscript) \
                            and isinstance(git.value, ast.Name) \
                            and git.value.id in lc.lists \
                            and isinstance(git.slice, ast.Slice) \
                            and git.slice.lower is None \
                            and git.slice.step is None \
                            and git.slice.upper is not None \
                            and lc.take_idx is not None \
                            and isinstance(git.slice.upper, ast.Name) \
                            and git.slice.upper.id == lc.take_idx:
                        up = _lref(git.slice.upper.id, rename)
                        return (f"(VeriPy.PySum (("
                                f"{_lref(git.value.id, rename)}.take "
                                f"({up}).toNat).map {gfn}))")
                raise _reject(
                    "a generator sum folds `f(x) for x in xs` or "
                    "`... in xs[:i]` (loop index bound) in this slice",
                    line)
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
    if isinstance(e, ast.IfExp):
        # `A if C else B` in a SPEC position is Lean's ite; the
        # condition rides the same decidability the Bool bridge uses
        # (linear comparisons synthesize Decidable instances). The
        # intersperse class needs it for the conditional length.
        _reject_undecidable_quantifier(e.test, names, line, lc)
        c = _prop_expr(e.test, names, line, result, rename, lc=lc)
        a = _int_expr(e.body, names, line, result, rename, lc)
        b = _int_expr(e.orelse, names, line, result, rename, lc)
        return f"(if {c} then {a} else {b})"
    raise _reject(f"expression {ast.dump(e)[:60]}... is outside slice 1",
                  line)



def _list_term(e: ast.expr, names: set[str], line: int,
               lc: "_ListCtx",
               rename: dict[str, str] | None = None) -> str | None:
    """A LIST-VALUED expression in a claim: comprehension over a list
    parameter or its nonnegative-bounded prefix, the parameter itself,
    such a prefix, a literal, or `+`-concatenation of these. Returns
    None when the expression is not list-shaped (the caller falls back
    to the scalar reading).

    Prefix bounds are restricted to shapes that are PROVABLY
    nonnegative from position alone -- the loop index, index plus a
    nonnegative literal, `len(L)`, or a literal -- because Python's
    negative slice bound means suffix-trimming, which `take`'s toNat
    clamp does not model."""
    def _upper_ok(u: ast.expr) -> str | None:
        if isinstance(u, ast.Constant) and isinstance(u.value, int) \
                and not isinstance(u.value, bool) and u.value >= 0:
            return str(u.value)
        if isinstance(u, ast.Name) and lc.take_idx is not None \
                and u.id == lc.take_idx:
            return _ident(u.id)
        if isinstance(u, ast.BinOp) and isinstance(u.op, ast.Add) \
                and isinstance(u.left, ast.Name) \
                and lc.take_idx is not None \
                and u.left.id == lc.take_idx \
                and isinstance(u.right, ast.Constant) \
                and isinstance(u.right.value, int) \
                and not isinstance(u.right.value, bool) \
                and u.right.value >= 0:
            return f"({_ident(u.left.id)} + {u.right.value})"
        if isinstance(u, ast.Call) and isinstance(u.func, ast.Name) \
                and u.func.id == "len" and len(u.args) == 1 \
                and not u.keywords and isinstance(u.args[0], ast.Name) \
                and u.args[0].id in lc.lists:
            return f"(({_lref(u.args[0].id, rename)}.length : Int))"
        return None

    def _iter_term(it: ast.expr) -> str | None:
        if isinstance(it, ast.Name) and it.id in lc.lists:
            return _lref(it.id, rename)
        if isinstance(it, ast.Subscript) \
                and isinstance(it.value, ast.Name) \
                and it.value.id in lc.lists \
                and isinstance(it.slice, ast.Slice) \
                and it.slice.lower is None and it.slice.step is None \
                and it.slice.upper is not None:
            up = _upper_ok(it.slice.upper)
            if up is not None:
                return f"({_lref(it.value.id, rename)}.take ({up}).toNat)"
        return None

    if isinstance(e, ast.ListComp) and len(e.generators) == 1 \
            and not e.generators[0].ifs \
            and not e.generators[0].is_async \
            and isinstance(e.generators[0].target, ast.Name):
        base = _iter_term(e.generators[0].iter)
        if base is not None:
            v = e.generators[0].target.id
            if v in names:
                raise _reject(f"comprehension binder {v!r} shadows a "
                              f"name in scope — outside this slice",
                              line)
            # The rename reaches EVERY scalar inside a list term:
            # threading it to the list names alone left a comprehension
            # body's `f` naming the function (review-caught, the
            # half-threaded variant of the previous finding).
            body = _int_expr(e.elt, names | {v}, line, rename=rename,
                             lc=lc)
            return f"({base}.map (fun {_ident(v)} => {body}))"
        return None
    base = _iter_term(e)
    if base is not None:
        return base
    if isinstance(e, ast.List):
        if not e.elts:
            return "([] : List Int)"
        items = ", ".join(_int_expr(x, names, line,
                                    rename=rename, lc=lc)
                          for x in e.elts)
        return f"([{items}] : List Int)"
    if isinstance(e, ast.BinOp) and isinstance(e.op, ast.Add):
        a = _list_term(e.left, names, line, lc, rename)
        b = _list_term(e.right, names, line, lc, rename)
        if a is not None and b is not None:
            return f"({a} ++ {b})"
    return None



def _slice_extension_shape(e: ast.expr, idx: str,
                           lc: "_ListCtx",
                           names: frozenset[str] | set[str] = frozenset()
                           ) -> tuple[str, str] | None:
    """`[f(x) for x in L[:idx+1]] == [f(x) for x in L[:idx]] + [ELT]`
    -- the corpus's slice-extension hint. Returns (L, fn) translated,
    or None. The two comprehensions must share the list and the body;
    ELT is not checked -- the lemma produces `f (getD idx 0)` and a
    mismatched ELT simply fails the `exact` (defeq), falling back to
    the generic ladder."""
    if not (isinstance(e, ast.Compare) and len(e.ops) == 1
            and isinstance(e.ops[0], ast.Eq)):
        return None
    lhs, rhs = e.left, e.comparators[0]
    if not (isinstance(rhs, ast.BinOp) and isinstance(rhs.op, ast.Add)
            and isinstance(rhs.right, ast.List)
            and len(rhs.right.elts) == 1):
        return None

    def _comp(c: ast.expr) -> tuple[str, str, str, ast.expr] | None:
        if not (isinstance(c, ast.ListComp) and len(c.generators) == 1
                and not c.generators[0].ifs
                and isinstance(c.generators[0].target, ast.Name)
                and isinstance(c.generators[0].iter, ast.Subscript)):
            return None
        it = c.generators[0].iter
        if not (isinstance(it.value, ast.Name) and it.value.id in lc.lists
                and isinstance(it.slice, ast.Slice)
                and it.slice.lower is None and it.slice.step is None
                and it.slice.upper is not None):
            return None
        return (it.value.id, c.generators[0].target.id,
                ast.dump(c.elt), it.slice.upper)

    def _plain(c: ast.expr):
        if isinstance(c, ast.Subscript) \
                and isinstance(c.value, ast.Name) \
                and c.value.id in lc.lists \
                and isinstance(c.slice, ast.Slice) \
                and c.slice.lower is None and c.slice.step is None \
                and c.slice.upper is not None:
            return (c.value.id, None, None, c.slice.upper)
        return None

    a, b = _comp(lhs), _comp(rhs.left)
    if a is None and b is None:
        a, b = _plain(lhs), _plain(rhs.left)
    if a is None or b is None:
        return None
    if a[0] != b[0] or a[1] != b[1] or a[2] != b[2]:
        return None
    up_a, up_b = a[3], b[3]
    if not (isinstance(up_b, ast.Name) and up_b.id == idx
            and isinstance(up_a, ast.BinOp)
            and isinstance(up_a.op, ast.Add)
            and isinstance(up_a.left, ast.Name) and up_a.left.id == idx
            and isinstance(up_a.right, ast.Constant)
            and up_a.right.value == 1):
        return None
    if a[1] is None:
        return (_ident(a[0]), None)
    # Full scope for the mapped body -- a binder-only set rejected
    # `[x * c for x in ...]` with parameter c (review-caught) -- and a
    # DETECTOR never raises: an untranslatable body is just not this
    # shape, and the generic ladder gets its chance.
    try:
        body_t = _int_expr(lhs.elt, set(names) | {a[1]},
                           getattr(e, "lineno", 0) or 0, lc=lc)
    except EncodeError:
        return None
    return (_ident(a[0]), f"(fun {_ident(a[1])} => {body_t})")



def _is_sorted_unique_call(node: ast.Call) -> bool:
    """The ONE admitted `sorted` shape: `sorted(list(set(NAME)))` or
    `sorted(set(NAME))` — the sorted-unique class. Anything else
    keeps the pre-gate's rejection (bare `sorted(L)` preserves
    duplicates: a different function, a different lemma pack)."""
    if not (len(node.args) == 1 and not node.keywords):
        return False
    inner = node.args[0]
    if isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name) \
            and inner.func.id == "list" and len(inner.args) == 1 \
            and not inner.keywords:
        inner = inner.args[0]
    return (isinstance(inner, ast.Call)
            and isinstance(inner.func, ast.Name)
            and inner.func.id == "set" and len(inner.args) == 1
            and not inner.keywords
            and isinstance(inner.args[0], ast.Name))


def _computed_read_wf(expr: ast.expr, lc: "_ListCtx",
                      names: set[str]) -> ast.expr | None:
    """The WELL-FORMEDNESS obligation for an ensures clause: for every
    list read the scaffold would totalize (a computed index no
    structural rule licenses), a quantified `0 <= idx < len(L)` under
    the same binder prefix. One synthetic clause conjoining them all,
    or None when every read is structurally licensed.

    This is the Dafny parallel: where that backend emits an in-bounds
    VC per read, this one appends the same claim as an extra post --
    `xs[100] == 0` becomes unprovable instead of quietly true about
    getD's default (review-caught)."""
    obligations: list[ast.expr] = []

    def structurally_ok(sub: ast.Subscript) -> bool:
        idx = sub.slice
        lname = sub.value.id
        if lname == "result":
            # BOTH the gate's structural licenses, restated: the
            # binder-over-`range(len(result))` pair, and an index
            # safe for the list an earlier ensures proved result
            # matches (missing the second appended redundant
            # obligations and shifted the parity endgame's post
            # count — caught by the intersperse e2e).
            return (isinstance(idx, ast.Name)
                    and (lc.safe_idx.get(idx.id) == "@result"
                         or (lc.result_list is not None
                             and lc.safe_for(idx.id,
                                             lc.result_list))))
        if isinstance(idx, ast.Name) and lc.safe_for(idx.id, lname):
            return True
        if isinstance(idx, ast.Constant) and isinstance(idx.value, int) \
                and not isinstance(idx.value, bool) \
                and lc.literal_ok(idx.value, lname):
            return True
        if isinstance(idx, ast.UnaryOp) \
                and isinstance(idx.op, ast.USub) \
                and isinstance(idx.operand, ast.Constant) \
                and idx.operand.value == 1 \
                and (lc.min_len or {}).get(lname, 0) >= 1:
            return True
        return False

    def walk(e: ast.expr, prefix: list[ast.comprehension],
             wlc: "_ListCtx") -> None:
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) \
                and e.func.id in ("all", "any") and e.args \
                and isinstance(e.args[0], ast.GeneratorExp):
            gen = e.args[0]
            inner_lc = wlc
            for g in gen.generators:
                if isinstance(g.target, ast.Name):
                    inner_lc = _quantifier_body_lc(inner_lc, g)
            walk(gen.elt, prefix + list(gen.generators), inner_lc)
            return
        if isinstance(e, ast.Subscript) \
                and isinstance(e.value, ast.Name) \
                and (e.value.id in wlc.lists
                     or (e.value.id == "result"
                         and wlc.result_is_list)) \
                and not isinstance(e.slice, ast.Slice):
            # `result` reads ride the same rule: the scaffold
            # totalizes them now, so every one not licensed by the
            # binder-over-`range(len(result))` pair owes an
            # in-bounds conjunct (`len(result)` translates in posts).
            if not structurally_ok_in(e, wlc):
                idx = e.slice
                wf = ast.parse(
                    f"0 <= 0 and 0 < len({e.value.id})",
                    mode="eval").body
                wf.values[0].comparators[0] = copy.deepcopy(idx)
                wf.values[1].left = copy.deepcopy(idx)
                body: ast.expr = wf
                for g in reversed(prefix):
                    body = ast.Call(
                        func=ast.Name(id="all", ctx=ast.Load()),
                        args=[ast.GeneratorExp(
                            elt=body,
                            generators=[copy.deepcopy(g)])],
                        keywords=[])
                obligations.append(body)
        for child in ast.iter_child_nodes(e):
            if isinstance(child, ast.expr):
                walk(child, prefix, wlc)

    def structurally_ok_in(sub: ast.Subscript,
                           wlc: "_ListCtx") -> bool:
        nonlocal lc
        saved, lc = lc, wlc
        try:
            return structurally_ok(sub)
        finally:
            lc = saved

    walk(expr, [], lc)
    if not obligations:
        return None
    out = (obligations[0] if len(obligations) == 1
           else ast.BoolOp(op=ast.And(), values=obligations))
    ast.fix_missing_locations(ast.Expression(body=out))
    return out


def _quantifier_body_lc(lc: "_ListCtx",
                        g: ast.comprehension) -> "_ListCtx":
    """The safe/take context a single range-generator grants its body
    -- the same rules the translator applies, restated for the WF
    pre-pass."""
    if not (isinstance(g.iter, ast.Call)
            and isinstance(g.iter.func, ast.Name)
            and g.iter.func.id == "range"
            and isinstance(g.target, ast.Name)):
        return lc
    v = g.target.id
    args = g.iter.args
    hi = args[-1] if args else None
    lo_zero_or_nonneg = (len(args) == 1
                         or _nonneg_bound(args[0], lc))
    safe = {k: lst for k, lst in lc.safe_idx.items() if k != v}
    if lo_zero_or_nonneg and isinstance(hi, ast.Call) \
            and isinstance(hi.func, ast.Name) and hi.func.id == "len" \
            and len(hi.args) == 1 \
            and isinstance(hi.args[0], ast.Name) \
            and hi.args[0].id in lc.lists:
        safe[v] = hi.args[0].id
    # The translator's "@result" license, restated (missed at first:
    # `result[i]` under `forall i in range(len(result))` looked
    # unlicensed to the WF walk, and the redundant obligations
    # shifted the parity endgame's post count). Same strictness as
    # the translator: a ZERO lower bound, not merely nonnegative.
    lo_is_zero = (len(args) == 1
                  or (isinstance(args[0], ast.Constant)
                      and args[0].value == 0))
    if lo_is_zero and isinstance(hi, ast.Call) \
            and isinstance(hi.func, ast.Name) and hi.func.id == "len" \
            and len(hi.args) == 1 \
            and isinstance(hi.args[0], ast.Name) \
            and hi.args[0].id == "result" and lc.result_is_list:
        safe[v] = "@result"
    # PROGRESSIVE, like the translator: a nonneg binder joins the
    # nonneg set so the NEXT generator's `range(i + 1, ...)` lower
    # bound checks out (missed at first, and the pre-pass then
    # injected obligations for binder-safe nested-∃ reads).
    nn = (frozenset(lc.nonneg_names | {v}) if lo_zero_or_nonneg
          else lc.nonneg_names)
    return _ListCtx(lc.lists, safe, lc.take_idx, lc.scaffold,
                    lc.min_len, lc.pos_names, lc.result_list,
                    lc.result_is_list, nn)


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
    if len(gen.generators) > 1:
        # `exists i in R1, j in R2 :: P` UNROLLS into nested
        # single-binder quantifiers: the outer binds i, and its body
        # is the same quantifier over the remaining generators --
        # scoping flows naturally, since inner ranges may reference
        # outer binders (`range(i + 1, len(l))`), and the prelude's
        # IntBexDec composes over the nesting when the result lands
        # in a decide position.
        inner = ast.Call(
            func=ast.Name(id=e.func.id, ctx=ast.Load()),
            args=[ast.GeneratorExp(elt=gen.elt,
                                   generators=gen.generators[1:])],
            keywords=[])
        outer = ast.Call(
            func=ast.Name(id=e.func.id, ctx=ast.Load()),
            args=[ast.GeneratorExp(elt=inner,
                                   generators=[gen.generators[0]])],
            keywords=[])
        ast.copy_location(outer, e)
        ast.fix_missing_locations(outer)
        return _quantifier(outer, names, line, result, rename,
                           result_is_bool, avoid, lc)
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
    if isinstance(it, ast.Name) \
            and (it.id in (lc or _NO_LISTS).lists
                 or (it.id == "result" and result is not None
                     and (lc or _NO_LISTS).result_is_list)):
        # MEMBERSHIP domain (`forall x in xs ::`): the binder ranges
        # over the list's ELEMENTS, not its indices, so it grants no
        # safe-index or take license — and it SHADOWS any outer
        # licenses under its name. The desugarer spells `==>` as
        # `(not A) or B`; the arrow is recovered here — a brand-new
        # context with no prior scripts relying on the ∨ spelling —
        # so the filter class's count script can intro the
        # antecedent.
        lc_m = lc or _NO_LISTS
        v = comp.target.id
        if v in lc_m.lists:
            raise _reject(f"quantifier binder {v!r} shadows a list "
                          f"parameter — outside this slice", line)
        lst = result if it.id == "result" else _lref(it.id, rename)
        safe_m = {k: l_ for k, l_ in lc_m.safe_idx.items() if k != v}
        body_lc = _ListCtx(lc_m.lists, safe_m,
                           None if lc_m.take_idx == v else lc_m.take_idx,
                           lc_m.scaffold, lc_m.min_len,
                           frozenset(lc_m.pos_names - {v}),
                           lc_m.result_list, lc_m.result_is_list,
                           frozenset(lc_m.nonneg_names - {v}))
        body_rename = {k: r for k, r in (rename or {}).items() if k != v}
        binder = v
        if avoid:
            while binder in avoid:
                binder += "'"
        if binder != v:
            body_rename[v] = binder
        body_avoid = (avoid or frozenset()) | {binder}
        elt = gen.elt
        if e.func.id == "all" and isinstance(elt, ast.BoolOp) \
                and isinstance(elt.op, ast.Or) \
                and len(elt.values) == 2 \
                and isinstance(elt.values[0], ast.UnaryOp) \
                and isinstance(elt.values[0].op, ast.Not):
            ante = _prop_expr(elt.values[0].operand, names | {v}, line,
                              result, body_rename or None,
                              result_is_bool, body_avoid, body_lc)
            cons = _prop_expr(elt.values[1], names | {v}, line, result,
                              body_rename or None, result_is_bool,
                              body_avoid, body_lc)
            body_m = f"({ante} → {cons})"
        else:
            body_m = _prop_expr(elt, names | {v}, line, result,
                                body_rename or None, result_is_bool,
                                body_avoid, body_lc)
        if e.func.id == "all":
            return (f"(∀ {_ident(binder)} : Int, "
                    f"{_ident(binder)} ∈ {lst} → {body_m})")
        return (f"(∃ {_ident(binder)} : Int, "
                f"{_ident(binder)} ∈ {lst} ∧ {body_m})")
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
    if isinstance(hi_arg, ast.Call) \
            and isinstance(hi_arg.func, ast.Name) \
            and hi_arg.func.id == "len" and not hi_arg.keywords \
            and len(hi_arg.args) == 1 \
            and isinstance(hi_arg.args[0], ast.Name) \
            and hi_arg.args[0].id == "result" and lo_is_zero:
        # A binder over range(len(result)) may read result at itself
        # -- and this OVERRIDES the scaffold's param-list wildcard,
        # which the result branch does not read.
        safe[v] = "@result"
    elif (lo_is_zero
          or (len(it.args) == 2 and _nonneg_bound(it.args[0], lc))) \
            and isinstance(hi_arg, ast.Call) \
            and isinstance(hi_arg.func, ast.Name) \
            and hi_arg.func.id == "len" and not hi_arg.keywords \
            and len(hi_arg.args) == 1 \
            and isinstance(hi_arg.args[0], ast.Name) \
            and hi_arg.args[0].id in lc.lists:
        # In bounds needs 0 ≤ v ∧ v < len: the binder's own bound
        # gives lo ≤ v < len, so any provably-NONNEGATIVE lo licenses
        # the read -- `for j in range(i + 1, len(l))` with i the
        # (nonnegative) outer index is the nested-search inner window.
        safe[v] = hi_arg.args[0].id
    # A binder over a provably-NONNEGATIVE range licenses `xs[:v]`
    # exactly as the loop index does: Python's negative slice bound
    # means suffix-trimming, which take's toNat clamp does not model,
    # and the bound hypothesis `lo ≤ v` rules that out wherever the
    # body is evaluated. This is what lets an ensures say
    # `exists n in range(len(xs) + 1) :: sum(xs[:n]) < 0`
    # (the below_zero class).
    body_take = (v if (len(it.args) < 2
                       or _nonneg_bound(it.args[0], lc))
                 else (None if lc.take_idx == v else lc.take_idx))
    body_lc = _ListCtx(lc.lists, safe,
                       body_take,
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
        llc = lc or _NO_LISTS
        lt = _list_term(e.left, names, line, llc, rename)
        rt = _list_term(e.comparators[0], names, line, llc, rename)
        if lt is not None and rt is not None:
            eq = f"({lt} = {rt})"
            return eq if isinstance(e.ops[0], ast.Eq) else f"(¬{eq})"
        # A mixed reading falls THROUGH to the scalar path: its
        # messages are the established voice, and `result == xs`
        # (whole-list equality, deliberately unmodeled) must keep the
        # boundary message it has always had -- _list_term cannot see
        # `result`, so a mixed-side rejection here called two lists
        # "a list and a non-list" (caught by the pinned message test).
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
    if isinstance(e, ast.Compare) and len(e.ops) == 1 \
            and type(e.ops[0]) in (ast.Eq, ast.NotEq):
        # Whole-list equality (`result == [x for x in l if x > 0]`):
        # both sides must be list-valued terms; a mixed comparison
        # falls through to the generic paths, whose messages are
        # better.
        def _lterm(x: ast.expr) -> str | None:
            lc_ = lc or _NO_LISTS
            if isinstance(x, ast.Name) and x.id == "result" \
                    and result is not None and lc_.result_is_list:
                return result
            if isinstance(x, (ast.ListComp, ast.List)) \
                    or (isinstance(x, ast.Name) and x.id in lc_.lists):
                return _list_expr(x, names, line, lc_, rename, result)
            return None
        la, ra = _lterm(e.left), _lterm(e.comparators[0])
        if la is not None and ra is not None:
            eq = f"({la} = {ra})"
            return eq if isinstance(e.ops[0], ast.Eq) else f"(¬{eq})"
    if isinstance(e, ast.Compare) and len(e.ops) == 1 \
            and type(e.ops[0]) in (ast.In, ast.NotIn) \
            and isinstance(e.comparators[0], ast.Name) \
            and (e.comparators[0].id in (lc or _NO_LISTS).lists
                 or (e.comparators[0].id == "result"
                     and result is not None
                     and (lc or _NO_LISTS).result_is_list)):
        # `x in xs` on a list parameter (or a list-valued result) is
        # List membership — same shape as the membership quantifier's
        # domain, and Python's `in` on list[int] is exactly ∈ on the
        # embedded List Int.
        target = e.comparators[0]
        lst = result if target.id == "result" else _lref(target.id,
                                                         rename)
        a = _int_expr(e.left, names, line, result, rename, lc)
        mem = f"({a} ∈ {lst})"
        return mem if isinstance(e.ops[0], ast.In) else f"(¬{mem})"
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
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not) \
            and isinstance(e.operand, ast.Name) \
            and e.operand.id in (lc or _NO_LISTS).lists:
        # Python truthiness: `not xs` on a list is emptiness.
        return f"((({_lref(e.operand.id, rename)}.length : Int)) = 0)"
    if isinstance(e, ast.Name) and e.id in (lc or _NO_LISTS).lists:
        # ...and a bare list in bool position is nonemptiness.
        return f"(¬((({_lref(e.id, rename)}.length : Int)) = 0))"
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
    """Replace FREE names with whole EXPRESSIONS. Used to make a loop
    body's assignments sequential: each right-hand side is rewritten
    through the updates before it, so a step reading another
    accumulator sees its NEW value, exactly as CPython executes it.
    Substituting simultaneously would model a different program.

    Free means free: a comprehension binder SHADOWS the name inside
    its own scope (review-caught: a search test binding the
    accumulator's name came out as `for b + xs[i] in range(i)` — the
    binder itself replaced by the step), and Python evaluates only the
    FIRST generator's iterable in the enclosing scope. Store-context
    names are never touched."""

    def __init__(self, mapping: dict[str, ast.expr]) -> None:
        self.mapping = mapping

    def visit_Name(self, node: ast.Name) -> ast.expr:
        if isinstance(node.ctx, ast.Store):
            return node
        repl = self.mapping.get(node.id)
        if repl is None:
            return node
        return copy.deepcopy(repl)

    def _visit_comp(self, node: ast.expr) -> ast.expr:
        bound: set[str] = set()
        for gi, g in enumerate(node.generators):
            outer = self if gi == 0 else _SubstExprs(
                {k: v for k, v in self.mapping.items()
                 if k not in bound})
            g.iter = outer.visit(g.iter)
            for t in ast.walk(g.target):
                if isinstance(t, ast.Name):
                    bound.add(t.id)
            inner = _SubstExprs({k: v for k, v in self.mapping.items()
                                 if k not in bound})
            g.ifs = [inner.visit(c) for c in g.ifs]
        body_sub = _SubstExprs({k: v for k, v in self.mapping.items()
                                if k not in bound})
        if isinstance(node, ast.DictComp):
            node.key = body_sub.visit(node.key)
            node.value = body_sub.visit(node.value)
        else:
            node.elt = body_sub.visit(node.elt)
        return node

    visit_ListComp = _visit_comp
    visit_SetComp = _visit_comp
    visit_GeneratorExp = _visit_comp
    visit_DictComp = _visit_comp


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
            # Range-bounded ∃ IS decidable now: the prelude's
            # IntBexDec instance recurses on the width, and it
            # composes, so nested `any` flattens too. `all` (∀) keeps
            # the rejection until a ∀-instance earns its way in.
            if isinstance(node.func, ast.Name) \
                    and node.func.id == "any" \
                    and node.func.id not in names:
                continue
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
               lc: _ListCtx, rename: dict[str, str] | None = None,
               result: str | None = None) -> str:
    """A `List Int`-valued Lean term. `[f(x) for x in xs]` becomes
    `xs.map (fun x => f x)`, which is the same order and length as
    Python's comprehension. Filtered comprehensions change the length
    and stay out of this slice."""
    if isinstance(e, ast.Name) and e.id in lc.lists:
        return _lref(e.id, rename)
    if isinstance(e, ast.List):
        # A literal list, `[]` above all: it is what a guard returns in
        # `if not numbers: return []`.
        if not e.elts:
            return "([] : List Int)"
        items = ", ".join(_int_expr(x, names, line, result, rename,
                                     lc) for x in e.elts)
        return f"([{items}] : List Int)"
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) \
            and e.func.id == "sorted" and e.func.id not in names \
            and len(e.args) == 1 and not e.keywords:
        # `sorted(list(set(L)))` (and the equivalent `sorted(set(L))`)
        # is the sorted-unique class: one prelude function computes
        # it by insertion sort that DROPS duplicates, and the pack's
        # lemmas give strict adjacency plus both membership
        # directions. Bare `sorted(L)` (duplicates kept) is a
        # different function with a different lemma story — rejected
        # until that slice.
        inner0 = e.args[0]
        if isinstance(inner0, ast.Call) \
                and isinstance(inner0.func, ast.Name) \
                and inner0.func.id == "list" \
                and inner0.func.id not in names \
                and len(inner0.args) == 1 and not inner0.keywords:
            inner0 = inner0.args[0]
        if isinstance(inner0, ast.Call) \
                and isinstance(inner0.func, ast.Name) \
                and inner0.func.id == "set" \
                and inner0.func.id not in names \
                and len(inner0.args) == 1 and not inner0.keywords \
                and isinstance(inner0.args[0], ast.Name) \
                and inner0.args[0].id in lc.lists:
            _SORTED_UNIQUE_USED.append(True)
            return (f"(VeriPy.SortedUnique "
                    f"{_lref(inner0.args[0].id, rename)})")
        raise _reject(
            "`sorted` is admitted only as `sorted(list(set(L)))` or "
            "`sorted(set(L))` over a list parameter in this slice — "
            "bare `sorted(L)` keeps duplicates, a different function "
            "with a different lemma pack", line)
    if isinstance(e, ast.ListComp):
        if len(e.generators) != 1:
            raise _reject("only one comprehension generator in this "
                          "slice", line)
        comp = e.generators[0]
        if comp.is_async:
            raise _reject("async comprehensions are outside this slice",
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
        if comp.ifs:
            # The filtered-comprehension class: ONLY the identity
            # element (`[x for x in xs if P]`), so the result is
            # `xs.filter` and Count_filter_of_pos speaks about it
            # directly. A mapped-and-filtered body would need a
            # composed story none of the ladder knows yet.
            if len(comp.ifs) != 1:
                raise _reject("one filter condition per comprehension "
                              "in this slice", line)
            if not (isinstance(e.elt, ast.Name) and e.elt.id == v):
                raise _reject(
                    "a FILTERED comprehension keeps elements unchanged "
                    "in this slice — `[x for x in xs if P]`; mapping "
                    "and filtering at once is outside it", line)
            test = _prop_expr(comp.ifs[0], names | {v}, line, result,
                              rename, lc=lc)
            pred = f"(fun {_ident(v)} : Int => (decide {test}))"
            if pred not in _FILTER_PREDS:
                _FILTER_PREDS.append(pred)
            return f"({_lref(comp.iter.id, rename)}.filter {pred})"
        body = _int_expr(e.elt, names | {v}, line, result, rename, lc)
        return (f"({_lref(comp.iter.id, rename)}.map "
                f"(fun {_ident(v)} => {body}))")
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
    if isinstance(head, ast.Assert):
        # An assert does not change the VALUE; it is a proof obligation,
        # emitted as its own theorem beside the function.
        return _body_expr(rest, names, params, is_bool, lc, is_list)
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
    # `for i in range(start, bound)` (P2 slice 19). None means 0 — and
    # None also keeps the 1-arg emission byte-identical to what every
    # pinned test expects.
    start: ast.expr | None = None
    # Leading `if COND: return V` guards, in source order. They
    # short-circuit before the loop runs.
    guards: list[tuple[ast.expr, ast.expr]] = field(default_factory=list)
    # The SEARCH-ACCUMULATOR shape (P2 slice 24, the below_zero
    # class): the body updates the accumulator, then early-returns a
    # bool literal when a test over the NEW value fires; the trailing
    # return is the complement literal. Modeled as a completed
    # (Int × Bool) fold -- the value result is identical because the
    # flag is or-monotone and the body is pure, the same argument the
    # slice-3 desugar documents.
    search_test: ast.expr | None = None
    search_hit: bool | None = None
    # The or-accumulator wrapped a ∀-clean invariant through a ¬
    # (nested-search class): preservation and endgame need the
    # duality scripts, at this quantifier depth.
    neg_wrap_depth: int = 0
    # Trailing `acc.append(E)` calls between the loop and the return
    # (P2 slice 25, the intersperse class): the returned value is the
    # fold result with the appended elements concatenated, so the
    # model is `fold ++ [e1] ++ ...`. List accumulators only, and the
    # appended expressions read parameters only -- the loop state they
    # could mention is exactly what the for path has no exit story
    # for.
    post_appends: list[ast.expr] = field(default_factory=list)
    # Trailing `assert`s between the loop and the return (P2 slice
    # 23). PARAMETERS-ONLY claims: the for path has no exit-state
    # machinery (that is the while path's), so a claim naming the
    # index or accumulator is rejected rather than stated about the
    # wrong state. Each becomes a theorem under the requires, and the
    # proved form is substituted into the spec proof.
    post_asserts: list[ast.Assert] = field(default_factory=list)
    # Top-level `assert`s in the loop BODY (P2 slice 18). Dafny reads
    # one as prove-then-assume, and so does this: each becomes its own
    # theorem under the invariant at that iteration, then rides into
    # the preservation step as a hypothesis. The two halves are what
    # make it a HINT rather than either an unchecked assumption or
    # dead weight.
    asserts: list[ast.Assert] = field(default_factory=list)



@dataclass(frozen=True)
class _OptMaxShape:
    """The OptionalMax class (rolling_max / he_9): an `int | None`
    running accumulator beside a list builder."""
    lst: str
    index: str
    opt: str
    builder: str
    elem: str
    has_assert: bool
    for_line: int
    inv_line: int
    ens_line: int
    assert_line: int


_OPTMAX_INTERNALS = frozenset({
    "m_", "i_", "rm_", "mx_", "n_", "v_", "k_", "k2_", "hd_", "hd0_",
    "hd1_", "hstep", "hinv", "hidx", "hilen", "hnnil", "hmx0", "hmxnil",
    "hi0", "hlen_pos", "hv", "hi_ge1", "htake", "hkold", "hkeq", "hk0",
    "hk2", "hn", "he", "h1", "h2", "h3", "h4", "g1", "g2", "g3", "g4",
    "hx2",
})


def _optional_max_shape(fn: ast.FunctionDef, spec_fn: FunctionSpec,
                        lists: frozenset[str]) -> _OptMaxShape | None:
    """Match the OptionalMax class STRICTLY, or decline (None) when the
    skeleton is absent. The class is matched, not translated: every
    invariant and ensures is required to be byte-shape-identical (names
    aside) to the rolling_max pattern, so emitting the proven template
    IS emitting the translation — the strictness is what makes that
    equation true, and near-misses are rejected with the pattern named
    rather than mistranslated. The `int | None` accumulator is modeled
    as `Option Int`, with `X == E` spelled `X = some E` (Python's
    `None == int` is False, and so is `none = some e` — the spelling is
    faithful on BOTH constructors, unlike a `getD` read).

    The optional in-loop `assert L[:i+1] == L[:i] + [L[i]]` is the
    slice-extension hint: it becomes its own theorem, proved by the
    prelude's Take_succ_getD (a runtime check in CPython, a VC in
    Dafny, a named lemma here)."""
    body = fn.body
    if len(body) != 4:
        return None
    s0, s1, s2, s3 = body
    # X: int | None = None
    if not (isinstance(s0, ast.AnnAssign) and isinstance(s0.target, ast.Name)
            and isinstance(s0.annotation, ast.BinOp)
            and isinstance(s0.annotation.op, ast.BitOr)
            and isinstance(s0.annotation.left, ast.Name)
            and s0.annotation.left.id == "int"
            and isinstance(s0.annotation.right, ast.Constant)
            and s0.annotation.right.value is None
            and isinstance(s0.value, ast.Constant)
            and s0.value.value is None):
        return None
    opt = s0.target.id
    # Y: list[int] = []
    if not (isinstance(s1, ast.AnnAssign) and isinstance(s1.target, ast.Name)
            and isinstance(s1.value, ast.List) and not s1.value.elts):
        return None
    builder = s1.target.id
    if not (isinstance(s2, ast.For) and not s2.orelse
            and isinstance(s2.target, ast.Name)
            and isinstance(s3, ast.Return)
            and isinstance(s3.value, ast.Name)
            and s3.value.id == builder):
        return None
    index = s2.target.id
    it = s2.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
            and it.func.id == "range" and len(it.args) == 1
            and not it.keywords and isinstance(it.args[0], ast.Call)
            and isinstance(it.args[0].func, ast.Name)
            and it.args[0].func.id == "len"
            and len(it.args[0].args) == 1
            and isinstance(it.args[0].args[0], ast.Name)
            and it.args[0].args[0].id in lists):
        return None
    lst = it.args[0].args[0].id

    def expect(actual: ast.expr, source: str, what: str,
               line: int) -> None:
        want = ast.parse(source, mode="eval").body
        if ast.dump(actual) != ast.dump(want):
            raise _reject(
                f"the OptionalMax class (an `int | None` running "
                f"accumulator beside a list builder) admits exactly "
                f"the rolling_max pattern; its {what} must be "
                f"`{source}`", line)

    # Loop body: n = L[i]; if X is None: X = n else: X = max(X, n);
    # optional slice-extension assert; Y.append(X)
    lb = list(s2.body)
    if not (3 <= len(lb) <= 4 and isinstance(lb[0], ast.Assign)
            and len(lb[0].targets) == 1
            and isinstance(lb[0].targets[0], ast.Name)):
        raise _reject(
            "the OptionalMax class loop body is exactly `n = L[i]`, "
            "the None-guarded max update, an optional slice-extension "
            "assert, and `maxes.append(running)`", s2.lineno)
    elem = lb[0].targets[0].id
    expect(lb[0].value, f"{lst}[{index}]",
           "element read", lb[0].lineno)
    ifst = lb[1]
    if not isinstance(ifst, ast.If):
        raise _reject("the OptionalMax class updates through "
                      "`if X is None: ... else: ...`", lb[1].lineno)
    expect(ifst.test, f"{opt} is None", "guard", ifst.lineno)
    if not (len(ifst.body) == 1 and isinstance(ifst.body[0], ast.Assign)
            and len(ifst.orelse) == 1
            and isinstance(ifst.orelse[0], ast.Assign)):
        raise _reject("the OptionalMax class updates the accumulator "
                      "in BOTH branches", ifst.lineno)
    bthen, belse = ifst.body[0], ifst.orelse[0]
    if not (len(bthen.targets) == 1
            and isinstance(bthen.targets[0], ast.Name)
            and bthen.targets[0].id == opt
            and len(belse.targets) == 1
            and isinstance(belse.targets[0], ast.Name)
            and belse.targets[0].id == opt):
        raise _reject("the OptionalMax class updates the SAME "
                      "accumulator in both branches", ifst.lineno)
    expect(bthen.value, f"{elem}", "None-branch update", bthen.lineno)
    expect(belse.value, f"max({opt}, {elem})", "else-branch update",
           belse.lineno)
    has_assert = len(lb) == 4
    assert_line = s2.lineno
    if has_assert:
        ast_a = lb[2]
        if not isinstance(ast_a, ast.Assert):
            raise _reject("the OptionalMax class admits one optional "
                          "assert, before the append", lb[2].lineno)
        expect(ast_a.test,
               f"{lst}[:{index} + 1] == {lst}[:{index}] + "
               f"[{lst}[{index}]]",
               "assert (the slice-extension hint)", ast_a.lineno)
        assert_line = ast_a.lineno
    app = lb[-1]
    ok_app = (isinstance(app, ast.Expr) and isinstance(app.value, ast.Call)
              and isinstance(app.value.func, ast.Attribute)
              and app.value.func.attr == "append"
              and isinstance(app.value.func.value, ast.Name)
              and app.value.func.value.id == builder
              and len(app.value.args) == 1
              and isinstance(app.value.args[0], ast.Name)
              and app.value.args[0].id == opt)
    if not ok_app:
        raise _reject("the OptionalMax class ends its loop body with "
                      "`maxes.append(running)`", app.lineno)

    # Invariants: the four, in order, exactly.
    invs = spec_fn.by_kind("invariant")
    if len(invs) != 4:
        raise _reject(
            "the OptionalMax class needs exactly its four invariants "
            "(builder length, None-iff-empty, the guarded running "
            "value, and the prefix-max ∀)", s2.lineno)
    inv_texts = [c.desugared if c.desugared is not None else c.raw
                 for c in invs]
    parsed = []
    for c, text in zip(invs, inv_texts):
        try:
            parsed.append(ast.parse(text, mode="eval").body)
        except SyntaxError as exc:
            raise _reject(f"cannot parse invariant: {exc.msg}", c.line)
    kb = "k"
    # The prefix-∀ binder name is the one free choice in the invariant
    # set; recover it so `expect` can name the exact source.
    if isinstance(parsed[3], ast.Call) and parsed[3].args             and isinstance(parsed[3].args[0], ast.GeneratorExp)             and isinstance(parsed[3].args[0].generators[0].target,
                           ast.Name):
        kb = parsed[3].args[0].generators[0].target.id
    expect(parsed[0], f"len({builder}) == {index}",
           "first invariant", invs[0].line)
    expect(parsed[1],
           f"bool({opt} is None) == bool(len({builder}) == 0)",
           "second invariant (spelled with <==>)", invs[1].line)
    expect(parsed[2],
           f"{opt} is None or {opt} == max({lst}[:len({builder})])",
           "third invariant", invs[2].line)
    expect(parsed[3],
           f"all(({builder}[{kb}] == max({lst}[:{kb} + 1])) "
           f"for {kb} in range(len({builder})))",
           "fourth invariant (spelled with forall)", invs[3].line)

    # Ensures: the two, in order, exactly.
    posts = spec_fn.by_kind("ensures")
    if len(posts) != 2:
        raise _reject("the OptionalMax class states exactly two "
                      "ensures (result length, and the prefix-max ∀)",
                      spec_fn.lineno)
    post_texts = [c.desugared if c.desugared is not None else c.raw
                  for c in posts]
    pp = []
    for c, text in zip(posts, post_texts):
        try:
            pp.append(ast.parse(text, mode="eval").body)
        except SyntaxError as exc:
            raise _reject(f"cannot parse ensures: {exc.msg}", c.line)
    ib = "i"
    if isinstance(pp[1], ast.Call) and pp[1].args             and isinstance(pp[1].args[0], ast.GeneratorExp)             and isinstance(pp[1].args[0].generators[0].target, ast.Name):
        ib = pp[1].args[0].generators[0].target.id
    expect(pp[0], f"len(result) == len({lst})",
           "first ensures", posts[0].line)
    expect(pp[1],
           f"all((result[{ib}] == max({lst}[:{ib} + 1])) "
           f"for {ib} in range(len({lst})))",
           "second ensures (spelled with forall)", posts[1].line)

    if spec_fn.by_kind("requires") or spec_fn.by_kind("proof")             or spec_fn.by_kind("decreases"):
        raise _reject("the OptionalMax class carries no requires, "
                      "proof, or decreases clauses", spec_fn.lineno)
    names_used = {node.id for node in ast.walk(fn)
                  if isinstance(node, ast.Name)} | {fn.name}
    if names_used & _OPTMAX_INTERNALS:
        raise _reject(
            "a name in this function collides with the OptionalMax "
            "template's internal binders (the *_-suffixed set) — "
            "rename it", fn.lineno)
    return _OptMaxShape(lst=lst, index=index, opt=opt, builder=builder,
                        elem=elem, has_assert=has_assert,
                        for_line=s2.lineno, inv_line=invs[0].line,
                        ens_line=posts[0].line,
                        assert_line=assert_line)



def _emit_optional_max(om: _OptMaxShape, fn: ast.FunctionDef,
                       spec_fn: FunctionSpec, emit, theorems) -> None:
    """Emit the OptionalMax class whole: fold over (Option Int × List
    Int), the invariant Prop, the induction theorem whose succ case
    splits on the constructor, the optional slice-extension assert
    theorem, and the spec theorem. The scripts are the PINNED template
    (proved end to end before this emitter existed); the matcher's
    strictness is what lets the template stand in for translation."""
    f = _ident(spec_fn.name)
    L = _ident(om.lst)
    fl = _ident(f"{spec_fn.name}_loop")
    fi = _ident(f"{spec_fn.name}_inv")
    fli = _ident(f"{spec_fn.name}_loop_inv")
    fsp = f"{spec_fn.name}_spec"
    fas = f"{spec_fn.name}_assert0"
    IL, EL, SL = om.inv_line, om.ens_line, om.assert_line

    emit("", None)
    emit(f"def {fl} ({L} : List Int) : Nat → Int → Option Int → "
         f"List Int → (Option Int × List Int)", om.for_line)
    emit("  | 0, _, rm_, mx_ => (rm_, mx_)", om.for_line)
    emit("  | (m_ + 1), i_, rm_, mx_ =>", om.for_line)
    emit(f"      let n_ : Int := {L}.getD (i_).toNat 0", om.for_line)
    emit("      let rm2_ : Option Int := match rm_ with", om.for_line)
    emit("        | none => some n_", om.for_line)
    emit("        | some v_ => some (max v_ n_)", om.for_line)
    emit(f"      {fl} {L} m_ (i_ + 1) rm2_ (mx_ ++ [rm2_.getD 0])",
         om.for_line)
    emit("", None)
    emit(f"def {f} ({L} : List Int) : List Int :=", om.for_line)
    emit(f"  ({fl} {L} ((({L}.length : Int))).toNat 0 none []).2",
         om.for_line)
    emit("", None)
    emit(f"def {fi} ({L} : List Int) (i_ : Int) (rm_ : Option Int) "
         f"(mx_ : List Int) : Prop :=", IL)
    emit("  (((mx_.length : Int)) = i_)", IL)
    emit("  ∧ ((rm_ = none) ↔ (((mx_.length : Int)) = 0))", IL)
    emit(f"  ∧ ((rm_ = none) ∨ (rm_ = some (VeriPy.ListMax "
         f"({L}.take ((mx_.length : Int)).toNat))))", IL)
    emit("  ∧ (∀ k_ : Int, (0 ≤ k_ ∧ k_ < ((mx_.length : Int))) →", IL)
    emit(f"       ((mx_.getD (k_).toNat 0) = VeriPy.ListMax "
         f"({L}.take ((k_ + 1)).toNat)))", IL)
    if om.has_assert:
        emit("", None)
        theorems.append(fas)
        emit(f"theorem {_ident(fas)} ({L} : List Int) : ∀ i_ : Int, "
             f"0 ≤ i_ → i_ < (({L}.length : Int)) →", SL)
        emit(f"    {L}.take ((i_ + 1)).toNat = {L}.take ((i_)).toNat "
             f"++ [{L}.getD (i_).toNat 0] := by", SL)
        emit("  intro i_ hd0_ hd1_", SL)
        emit(f"  have hn := VeriPy.Take_succ_getD {L} (i_).toNat "
             f"(by omega)", SL)
        emit("  rw [show ((i_).toNat + 1) = ((i_ + 1)).toNat from by "
             "omega] at hn", SL)
        emit("  exact hn", SL)
    emit("", None)
    theorems.append(f"{spec_fn.name}_loop_inv")
    emit(f"theorem {fli} ({L} : List Int) : ∀ (m_ : Nat) (i_ : Int) "
         f"(rm_ : Option Int) (mx_ : List Int),", IL)
    emit(f"    {fi} {L} i_ rm_ mx_ → 0 ≤ i_ → "
         f"i_ + (m_ : Int) ≤ max ((({L}.length : Int))) i_ →", IL)
    emit(f"    {fi} {L} (i_ + m_)", IL)
    emit(f"      ({fl} {L} m_ i_ rm_ mx_).1 "
         f"({fl} {L} m_ i_ rm_ mx_).2 := by", IL)
    emit("  intro m_", IL)
    emit("  induction m_ with", IL)
    emit("  | zero =>", IL)
    emit("      intro i_ rm_ mx_ h1 hd0_ hd1_", IL)
    emit(f"      simpa only [{fl}, Int.natCast_zero, Int.add_zero] "
         f"using h1", IL)
    emit("  | succ k_ ih =>", IL)
    emit("      intro i_ rm_ mx_ h1 hd0_ hd1_", IL)
    emit("      obtain ⟨h1, h2, h3, h4⟩ := h1", IL)
    emit(f"      have hilen : i_ < ({L}.length : Int) := by omega", IL)
    emit(f"      have hnnil : {L} ≠ [] := by", IL)
    emit("        intro he; rw [he] at hilen; simp at hilen; omega", IL)
    emit("      have hidx : i_ + 1 + (k_ : Int) = "
         "i_ + ((k_ + 1 : Nat) : Int) := by", IL)
    emit("        push_cast; omega", IL)
    emit("      cases rm_ with", IL)
    emit("      | none =>", IL)
    emit("          have hmx0 : ((mx_.length : Int)) = 0 := h2.mp rfl",
         IL)
    emit("          have hmxnil : mx_ = [] := by", IL)
    emit("            have hn : mx_.length = 0 := by omega", IL)
    emit("            exact List.eq_nil_of_length_eq_zero hn", IL)
    emit("          have hi0 : i_ = 0 := by omega", IL)
    emit("          subst hmxnil", IL)
    emit(f"          simp only [{fl}]", IL)
    emit(f"          have hstep := ih (i_ + 1) "
         f"(some ({L}.getD (i_).toNat 0))", IL)
    emit(f"            [{L}.getD (i_).toNat 0]", IL)
    emit("            ?_ (by omega) (by (try push_cast at hd1_ ⊢); "
         "omega)", IL)
    emit("          · rw [hidx] at hstep", IL)
    emit("            exact hstep", IL)
    emit("          · refine ⟨by simp; omega, by simp, Or.inr ?_, "
         "?_⟩", IL)
    emit("            · simp only [List.length_cons, List.length_nil]",
         IL)
    emit("              rw [show ((((1 : Nat) : Int)).toNat = 1) "
         "from rfl]", IL)
    emit(f"              rw [VeriPy.ListMax_take_one {L} hnnil]", IL)
    emit("              rw [show (i_).toNat = 0 from by omega]", IL)
    emit("            · intro k2_ hk2", IL)
    emit("              simp only [List.length_cons, List.length_nil] "
         "at hk2", IL)
    emit("              have hk0 : k2_ = 0 := by push_cast at hk2; "
         "omega", IL)
    emit("              subst hk0", IL)
    emit("              simp only [Int.toNat_zero, "
         "List.getD_cons_zero]", IL)
    emit("              rw [show (((0 : Int) + 1)).toNat = 1 from "
         "rfl]", IL)
    emit(f"              rw [VeriPy.ListMax_take_one {L} hnnil]", IL)
    emit("              rw [show (i_).toNat = 0 from by omega]", IL)
    emit("      | some v_ =>", IL)
    emit("          have hlen_pos : ((mx_.length : Int)) ≠ 0 := by",
         IL)
    emit("            intro he", IL)
    emit("            have hx2 := h2.mpr he", IL)
    emit("            simp at hx2", IL)
    emit(f"          have hv : v_ = VeriPy.ListMax ({L}.take "
         f"((mx_.length : Int)).toNat) := by", IL)
    emit("            rcases h3 with h3 | h3", IL)
    emit("            · exact absurd h3 (by simp)", IL)
    emit("            · simpa using h3", IL)
    emit("          have hi_ge1 : 1 ≤ i_ := by omega", IL)
    emit(f"          have htake : VeriPy.ListMax ({L}.take "
         f"((i_ + 1)).toNat)", IL)
    emit(f"              = max (VeriPy.ListMax ({L}.take (i_).toNat)) "
         f"({L}.getD (i_).toNat 0) := by", IL)
    emit(f"            have hn := VeriPy.ListMax_take_succ {L} "
         f"(i_).toNat", IL)
    emit("              (by omega) (by omega)", IL)
    emit("            rw [show ((i_).toNat + 1) = ((i_ + 1)).toNat "
         "from by omega] at hn", IL)
    emit("            exact hn", IL)
    emit(f"          simp only [{fl}]", IL)
    emit(f"          have hstep := ih (i_ + 1) (some (max v_ "
         f"({L}.getD (i_).toNat 0)))", IL)
    emit(f"            (mx_ ++ [max v_ ({L}.getD (i_).toNat 0)])", IL)
    emit("            ?_ (by omega) (by (try push_cast at hd1_ ⊢); "
         "omega)", IL)
    emit("          · rw [hidx] at hstep", IL)
    emit("            exact hstep", IL)
    emit("          · refine ⟨?_, ?_, Or.inr ?_, ?_⟩", IL)
    emit("            · simp [List.length_append]; omega", IL)
    emit("            · constructor", IL)
    emit("              · intro he; simp at he", IL)
    emit("              · intro he", IL)
    emit("                exact absurd he (by "
         "simp [List.length_append]; omega)", IL)
    emit(f"            · rw [show ((((mx_ ++ [max v_ ({L}.getD "
         f"(i_).toNat 0)]).length : Int)).toNat)", IL)
    emit("                    = ((i_ + 1)).toNat from by "
         "simp [List.length_append]; omega]", IL)
    emit("              rw [htake, hv]", IL)
    emit("              rw [show ((mx_.length : Int)).toNat = "
         "(i_).toNat from by omega]", IL)
    emit("            · intro k2_ hk2", IL)
    emit("              simp only [List.length_append, "
         "List.length_cons,", IL)
    emit("                         List.length_nil] at hk2", IL)
    emit("              push_cast at hk2", IL)
    emit("              by_cases hkold : k2_ < ((mx_.length : Int))",
         IL)
    emit(f"              · rw [VeriPy.GetD_append_left mx_ _ "
         f"(k2_).toNat (by omega)]", IL)
    emit("                exact h4 k2_ ⟨hk2.1, hkold⟩", IL)
    emit("              · have hkeq : k2_ = ((mx_.length : Int)) := "
         "by omega", IL)
    emit("                subst hkeq", IL)
    emit("                rw [show ((mx_.length : Int)).toNat = "
         "mx_.length from by omega]", IL)
    emit("                rw [VeriPy.GetD_append_last mx_ _]", IL)
    emit("                rw [show (((mx_.length : Int)) + 1).toNat "
         "= ((i_ + 1)).toNat", IL)
    emit("                      from by omega]", IL)
    emit("                rw [htake, hv]", IL)
    emit("                rw [show ((mx_.length : Int)).toNat = "
         "(i_).toNat from by omega]", IL)
    emit("", None)
    theorems.append(fsp)
    emit(f"theorem {_ident(fsp)} ({L} : List Int) :", EL)
    emit(f"    (((({f} {L}).length : Int)) = (({L}.length : Int)))",
         EL)
    emit(f"    ∧ (∀ i_ : Int, (0 ≤ i_ ∧ i_ < (({L}.length : Int))) →",
         EL)
    emit(f"        (({f} {L}).getD (i_).toNat 0", EL)
    emit(f"          = VeriPy.ListMax ({L}.take ((i_ + 1)).toNat))) "
         f":= by", EL)
    emit(f"  unfold {f}", EL)
    emit(f"  have hinv := {fli} {L} ((({L}.length : Int))).toNat 0 "
         f"none []", EL)
    emit("    ⟨by simp, by simp, Or.inl rfl, by intro k_ hk2; "
         "simp at hk2; omega⟩", EL)
    emit("    (by omega) (by omega)", EL)
    emit("  obtain ⟨g1, g2, g3, g4⟩ := hinv", EL)
    emit("  constructor", EL)
    emit("  · omega", EL)
    emit("  · intro i_ hd0_", EL)
    emit("    have hn := g4 i_ (by omega)", EL)
    emit("    simpa using hn", EL)


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



def _const_div_bridges(fn: ast.FunctionDef,
                       spec_fn: FunctionSpec) -> tuple[list[str], list[str]]:
    """Bridge `//` and `%` by a CONSTANT positive divisor to Lean's own
    `/` and `%`, which omega reasons about natively. Without this every
    floor-division goal is an opaque atom -- `0 = PyFloorDiv 0 2` does
    not close, and neither does anything downstream of it.

    One `have` per distinct divisor, QUANTIFIED over the dividend, so a
    single rewrite reaches every occurrence whatever shape the dividend
    has. Per-site rewriting with an exact term is what does not work
    here: the occurrence that matters is usually one the surrounding
    tactics have already reshaped, and the spelled-out term no longer
    matches it.

    Returns (have lines, hypothesis names).
    """
    div_c: set[int] = set()
    mod_c: set[int] = set()
    for _num, den, is_mod in _divmod_sites(fn, spec_fn):
        # `isinstance(True, int)` holds in Python, and `x // True` is a
        # different thing from `x // 1` to a reader, so bools are out.
        if isinstance(den, ast.Constant) and not isinstance(den.value, bool) \
                and isinstance(den.value, int) and den.value > 0:
            (mod_c if is_mod else div_c).add(den.value)
    haves: list[str] = []
    names: list[str] = []
    for c in sorted(div_c):
        nm = f"hfdb{c}"
        haves.append(f"have {nm} : ∀ a : Int, VeriPy.PyFloorDiv a {c} "
                     f"= a / {c} := fun a => VeriPy.PyFloorDiv_pos a {c} "
                     f"(by omega)")
        names.append(nm)
    for c in sorted(mod_c):
        nm = f"hmdb{c}"
        haves.append(f"have {nm} : ∀ a : Int, VeriPy.PyMod a {c} "
                     f"= a % {c} := fun a => VeriPy.PyMod_pos a {c} "
                     f"(by omega)")
        names.append(nm)
    return haves, names

def _wrap_guards(guards: list[tuple[ast.expr, ast.expr]], body: str,
                 names: set[str], line: int, lc: "_ListCtx",
                 is_bool: bool, is_list: bool = False) -> str:
    """Wrap a loop's value in its leading guards, innermost last.

    `if COND: return V` short-circuits before the loop runs, so it is
    `if COND then V else <rest>`. The generated proof needs nothing new:
    `repeat' split` in the cocktail already peels conditionals, and the
    loop facts are established before the split, so both branches see
    them."""
    out = body
    for cond, value in reversed(guards):
        _no_old(cond, line)
        _no_old(value, line)
        # A guard becomes a Lean `if`, which is a DECIDABLE position.
        # An `all`/`any` over Int has no Decidable instance, so emitting
        # it fails elaboration — and the failure surfaces as a prover
        # verdict, making an unsupported input look like a false spec.
        # The refusal has to happen here.
        _reject_undecidable_quantifier(cond, names, line, lc)
        cond_t = _prop_expr(cond, names, line, lc=lc)
        # The guard returns the FUNCTION's type, so a list-returning
        # function's guard yields a list — `if not numbers: return []`
        # is the opening line of intersperse. Sending it through the
        # integer encoder rejected a valid expression.
        if is_list:
            val_t = _list_expr(value, names, line, lc)
        elif is_bool:
            val_t = _bool_expr(value, names, line, lc)
        else:
            val_t = _int_expr(value, names, line, lc=lc)
        out = f"(if {cond_t} then {val_t} else {out})"
    return out


_AUG_OPS = (ast.Add, ast.Sub, ast.Mult)


def _collect_asserts(stmts: list[ast.stmt],
                     path: tuple[tuple[ast.expr, bool], ...] = (),
                     subst: dict[str, ast.expr] | None = None
                     ) -> list[tuple[ast.Assert, ast.expr,
                                     tuple[tuple[ast.expr, bool], ...]]]:
    """Every `assert` in a loop-free body, as (statement, claim, path).

    An assert is a claim about the state at ONE POINT in the body, and
    lifting it into a standalone theorem has to carry every way its
    meaning depends on that position. Four ways, each learned the hard
    way. The PATH CONDITION, because `if n > 0: assert P` owes P only
    when the branch is taken -- including the IMPLICIT else, since an
    `if` without `else` that returns makes everything after it the else
    branch. The NESTING, because reading only the top level dropped a
    nested obligation entirely. And the LOCALS: an obligation is a
    theorem over the function's parameters, so a local has no meaning
    in it -- `s = n + 1; assert s > 0` is the claim `n + 1 > 0`, and
    the local's definition is substituted in rather than its name
    carried out of scope."""
    out: list[tuple[ast.Assert, ast.expr,
                    tuple[tuple[ast.expr, bool], ...]]] = []
    live = dict(subst or {})
    for idx, st in enumerate(stmts):
        if isinstance(st, ast.Assert):
            claim = _SubstExprs(dict(live)).visit(copy.deepcopy(st.test))
            out.append((st, claim, path))
        elif isinstance(st, ast.Assign) and len(st.targets) == 1 \
                and isinstance(st.targets[0], ast.Name):
            live[st.targets[0].id] = _SubstExprs(dict(live)).visit(
                copy.deepcopy(st.value))
        elif isinstance(st, (ast.For, ast.While)):
            # A loop REBINDS names, and a name's post-loop value is not
            # its pre-loop definition. Substituting across the loop
            # would state a later obligation about the wrong state --
            # `s = n; while s > 0: s = s - 1; assert s == 0` would
            # become the false `n = 0`. Dropping them turns that into a
            # loud `unknown name` rather than a quiet wrong claim.
            # (The loop shapes reject this arrangement today; the guard
            # is here so admitting it later cannot go wrong silently.)
            for sub in ast.walk(st):
                if isinstance(sub, ast.Name) \
                        and isinstance(sub.ctx, ast.Store):
                    live.pop(sub.id, None)
        elif isinstance(st, ast.If):
            cond = _SubstExprs(dict(live)).visit(copy.deepcopy(st.test))
            out.extend(_collect_asserts(st.body, path + ((cond, True),),
                                        live))
            out.extend(_collect_asserts(st.orelse,
                                        path + ((cond, False),), live))
            if not st.orelse and _always_returns(st.body):
                # `_body_expr` compiles what FOLLOWS an `if` without
                # `else` as that `if`'s else branch, so those
                # statements run only when the test is false. Reading
                # on at this level instead owes the assert
                # unconditionally, which rejects a correct function.
                out.extend(_collect_asserts(stmts[idx + 1:],
                                            path + ((cond, False),),
                                            live))
                break
    return out


class _AugAssignRewriter(ast.NodeTransformer):
    """Rewrite every `x += e` to `x = x + e`, module-wide."""

    def visit_AugAssign(self, node: ast.AugAssign) -> ast.stmt:
        self.generic_visit(node)
        if not isinstance(node.target, ast.Name):
            return node
        if not isinstance(node.op, _AUG_OPS):
            raise _reject(
                f"augmented assignment `{type(node.op).__name__}` is "
                f"outside this slice — `+=`, `-=` and `*=` desugar to "
                f"their plain form", node.lineno)
        out = ast.Assign(
            targets=[ast.Name(id=node.target.id, ctx=ast.Store())],
            value=ast.BinOp(left=ast.Name(id=node.target.id,
                                          ctx=ast.Load()),
                            op=node.op, right=node.value))
        return ast.copy_location(out, node)


def _desugar_aug(st: ast.stmt) -> ast.stmt:
    """`x += e` is `x = x + e`. Desugaring here means every shape
    downstream sees one spelling, rather than each loop matcher growing
    a second case it might get subtly wrong.

    Only the operators the fragment already models are desugared; `x //=
    e` and friends keep their own refusal, which names the operator."""
    if not isinstance(st, ast.AugAssign) or not isinstance(st.target,
                                                           ast.Name):
        return st
    if not isinstance(st.op, _AUG_OPS):
        # Name the operator rather than letting the loop matcher report
        # a shape error: `s //= 2` is a fine Python statement, and the
        # honest complaint is about the operator, not the loop.
        raise _reject(
            f"augmented assignment `{type(st.op).__name__}` is outside "
            f"this slice — `+=`, `-=` and `*=` desugar to their plain "
            f"form", st.lineno)
    out = ast.Assign(
        targets=[ast.Name(id=st.target.id, ctx=ast.Store())],
        value=ast.BinOp(left=ast.Name(id=st.target.id, ctx=ast.Load()),
                        op=st.op, right=st.value))
    ast.copy_location(out, st)
    ast.fix_missing_locations(out)
    return out


def _split_guards(stmts: list[ast.stmt]
                  ) -> tuple[list[tuple[ast.expr, ast.expr]],
                             list[ast.stmt]]:
    """Leading `if COND: return V` guards, and the statements after
    them.

    A guard short-circuits before the loop ever runs, so it compiles to
    an `if COND then V else <the rest>` wrapped around the loop's value.
    `is_prime` opens with `if n < 2: return False` and `intersperse`
    with `if not numbers: return []`, and both are ordinary Python that
    the loop shapes would otherwise refuse."""
    guards: list[tuple[ast.expr, ast.expr]] = []
    i = 0
    while i < len(stmts):
        st = stmts[i]
        if not (isinstance(st, ast.If) and not st.orelse
                and len(st.body) == 1
                and isinstance(st.body[0], ast.Return)
                and st.body[0].value is not None):
            break
        guards.append((st.test, st.body[0].value))
        i += 1
    return guards, stmts[i:]


def _str_element_discipline(fn: ast.FunctionDef,
                            spec_fn: FunctionSpec,
                            str_params: frozenset[str]) -> None:
    """The code-point model (`str` as `List Int`) is faithful only
    where the admitted operations cannot tell a string from its
    code-point sequence: `len(s)`, and comparisons in which EVERY
    operand is a single-character read of a str parameter (Python
    compares characters by code point, so ==/!=/</<=/>/>= all
    transfer). Everything else is rejected by default — arithmetic on
    an element, `sum`, slices, whole-string comparison, iteration —
    rather than silently proved about a program that would raise
    TypeError or mean something different in Python. Ghost
    expressions (spec clauses) obey the same rule, so a `#@` clause
    keeps one meaning across backends. Shadowing a str parameter
    (a local or binder reusing the name) also rejects: over-strict
    is safe, and the fragment note says so.

    Every source of expressions is swept: the function body AST and
    every expression-kind spec clause. Clause text that fails to
    parse is skipped here — the clause's own translator rejects it
    with the better message."""
    def elem_read(e: ast.expr) -> bool:
        return (isinstance(e, ast.Subscript)
                and isinstance(e.value, ast.Name)
                and e.value.id in str_params
                and not isinstance(e.slice, ast.Slice))

    def sweep(root: ast.AST, clause_line: int | None) -> None:
        licensed: set[int] = set()
        for node in ast.walk(root):
            if isinstance(node, ast.Compare):
                operands = [node.left, *node.comparators]
                if any(elem_read(o) for o in operands):
                    if not all(elem_read(o) for o in operands):
                        raise _reject(
                            "a character of a `str` parameter can only "
                            "be compared with another character read "
                            "(the code-point model has no literals or "
                            "arithmetic in this slice)",
                            clause_line
                            or getattr(node, "lineno", None))
                    for o in operands:
                        licensed.add(id(o.value))
            elif (isinstance(node, ast.Call)
                    and isinstance(node.func, ast.Name)
                    and node.func.id == "len"
                    and len(node.args) == 1
                    and isinstance(node.args[0], ast.Name)
                    and node.args[0].id in str_params):
                licensed.add(id(node.args[0]))
        for node in ast.walk(root):
            if isinstance(node, ast.Name) and node.id in str_params \
                    and id(node) not in licensed:
                raise _reject(
                    f"`{node.id}` is a `str` parameter: this slice "
                    f"admits it only as `len({node.id})` or in "
                    f"comparisons between two indexed characters",
                    clause_line or getattr(node, "lineno", None))

    sweep(fn, None)
    for c in spec_fn.clauses:
        if c.kind not in ("ensures", "requires", "invariant", "assert") \
                or c.error is not None:
            continue
        text = c.desugared if c.desugared is not None else c.raw
        try:
            tree = ast.parse(text, mode="eval").body
        except SyntaxError:
            continue
        sweep(tree, c.line)


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
    misplaced = [c for c in every if c not in invs
                 and not any(lo < c.line <= hi
                             for lo, hi in _ABSORBED_INNER_SPANS)]
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


# Line spans of inner loops the nested-search flattener absorbed this
# encode: their invariants are the flag's meaning (carried by the
# synthesized existential) and stay live for the Dafny backend, so
# the misplacement rule skips them. Reset per encode_module_lean call.
_ABSORBED_INNER_SPANS: list[tuple[int, int]] = []


# The filter predicates emitted this encode (`[x for x in l if P]` ->
# `l.filter (fun v => decide P)`), as the exact lambda text: the spec
# theorem's ladder needs each one to instantiate Count_filter_of_pos
# explicitly (rw's higher-order unification cannot be trusted to
# reconstruct the pattern). Reset per encode_module_lean call.
_FILTER_PREDS: list[str] = []


# True when this encode emitted VeriPy.SortedUnique (the
# `sorted(list(set(l)))` class): the ladder then offers the pack's
# three spec-shaped lemmas as guarded finishers. Reset per
# encode_module_lean call.
_SORTED_UNIQUE_USED: list[bool] = []


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
    # `for i, x in enumerate(l)` normalizes to `for i in
    # range(len(l))` with x's free occurrences substituted by l[i]
    # (the substitution is LEXICAL, so binders shadowing x survive).
    if isinstance(loop.target, ast.Tuple) \
            and len(loop.target.elts) == 2 \
            and all(isinstance(t, ast.Name) for t in loop.target.elts) \
            and isinstance(loop.iter, ast.Call) \
            and isinstance(loop.iter.func, ast.Name) \
            and loop.iter.func.id == "enumerate" \
            and len(loop.iter.args) == 1 and not loop.iter.keywords \
            and isinstance(loop.iter.args[0], ast.Name):
        ivar, xvar = (t.id for t in loop.target.elts)
        lname = loop.iter.args[0].id
        repl = ast.parse(f"{lname}[{ivar}]", mode="eval").body
        loop = copy.deepcopy(loop)
        loop.target = ast.Name(id=ivar, ctx=ast.Store())
        loop.iter = ast.parse(f"range(len({lname}))", mode="eval").body
        loop.body = [_SubstExprs({xvar: repl}).visit(b)
                     for b in loop.body]
        ast.fix_missing_locations(loop)
    # A nested PURE search flattens: an inner
    # `for j in range(a, b): if TEST: return LIT` as the outer's only
    # statement becomes `if any(TEST for j in range(a, b)): return
    # LIT` -- the prelude's IntBexDec makes the bounded ∃ decidable,
    # and the instance composes, so deeper nestings flatten level by
    # level through this same rewrite. The inner loop's own
    # invariants are absorbed: they state the flag's meaning, which
    # the synthesized existential now carries (they remain live for
    # the Dafny backend, which walks the original source).
    def _flatten_innermost(fr: ast.For) -> bool:
        """Rewrite the DEEPEST `for j: if TEST: return LIT` under fr
        into its any-If form, one level per call. Returns True when a
        rewrite happened."""
        if not (len(fr.body) == 1 and isinstance(fr.body[0], ast.For)):
            return False
        child = fr.body[0]
        if _flatten_innermost(child):
            return True
        if not (isinstance(child.target, ast.Name)
                and isinstance(child.iter, ast.Call)
                and isinstance(child.iter.func, ast.Name)
                and child.iter.func.id == "range"
                and len(child.body) == 1
                and isinstance(child.body[0], ast.If)
                and not child.body[0].orelse
                and len(child.body[0].body) == 1
                and isinstance(child.body[0].body[0], ast.Return)):
            return False
        itest = child.body[0].test
        iret = child.body[0].body[0]
        gen = ast.GeneratorExp(
            elt=copy.deepcopy(itest),
            generators=[ast.comprehension(
                target=copy.deepcopy(child.target),
                iter=copy.deepcopy(child.iter), ifs=[],
                is_async=0)])
        newif = ast.If(
            test=ast.Call(func=ast.Name(id="any", ctx=ast.Load()),
                          args=[gen], keywords=[]),
            body=[copy.deepcopy(iret)], orelse=[])
        ast.copy_location(newif, child)
        fr.body = [newif]
        ast.fix_missing_locations(fr)
        _ABSORBED_INNER_SPANS.append((child.lineno, iret.lineno))
        return True

    if len(loop.body) == 1 and isinstance(loop.body[0], ast.For):
        loop = copy.deepcopy(loop)
        while _flatten_innermost(loop):
            pass
    while (len(loop.body) == 1 and isinstance(loop.body[0], ast.For)
           and isinstance(loop.body[0].target, ast.Name)
           and isinstance(loop.body[0].iter, ast.Call)
           and isinstance(loop.body[0].iter.func, ast.Name)
           and loop.body[0].iter.func.id == "range"
           and len(loop.body[0].body) == 1
           and isinstance(loop.body[0].body[0], ast.If)
           and not loop.body[0].body[0].orelse
           and len(loop.body[0].body[0].body) == 1
           and isinstance(loop.body[0].body[0].body[0], ast.Return)):
        inner = loop.body[0]
        itest = inner.body[0].test
        iret = inner.body[0].body[0]
        gen = ast.GeneratorExp(
            elt=copy.deepcopy(itest),
            generators=[ast.comprehension(
                target=copy.deepcopy(inner.target),
                iter=copy.deepcopy(inner.iter), ifs=[],
                is_async=0)])
        newtest = ast.Call(func=ast.Name(id="any", ctx=ast.Load()),
                           args=[gen], keywords=[])
        newif = ast.If(test=newtest,
                       body=[copy.deepcopy(iret)], orelse=[])
        ast.copy_location(newif, inner)
        loop = (loop if loop.body[0] is not inner else loop)
        loop = copy.deepcopy(loop)
        loop.body = [newif]
        ast.fix_missing_locations(loop)
        _ABSORBED_INNER_SPANS.append(
            (inner.lineno, iret.lineno))
    body = list(loop.body)
    if any(isinstance(s, ast.Assert) for s in body) \
            and len([s for s in body
                     if not isinstance(s, ast.Assert)]) == 1:
        raise _reject(
            "an `assert` in an early-return search loop is outside this "
            "slice — that shape is desugared into a SYNTHESIZED bool "
            "accumulator, so there is no invariant of the user's own "
            "for the obligation to be discharged under; an assert in a "
            "plain accumulator loop is admitted", body[0].lineno)
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
            and it.func.id == "range" and len(it.args) in (1, 2)
            and not it.keywords):
        raise _reject("loops must iterate `range(<bound>)` or "
                      "`range(<start>, <bound>)` in this slice "
                      "(a step is not modelled)", loop.lineno)
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
    # Spec comments are not in fn's AST: a quantifier binder named
    # `b` in an invariant or ensures collides with the synthesized
    # accumulator exactly as a code name would (measured on the
    # nested-search class, whose double-binder invariants use a, b).
    for kind in ("requires", "ensures", "invariant"):
        for c in spec_fn.by_kind(kind):
            text = c.desugared if c.desugared is not None else c.raw
            try:
                for node in ast.walk(ast.parse(text, mode="eval")):
                    if isinstance(node, ast.Name):
                        used.add(node.id)
            except SyntaxError:
                continue
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
    # The user's invariant states the still-searching prefix
    # property. For the AND-accumulator (return False on hit) the
    # accumulator tracks exactly that, so the iff is `acc == <inv>`.
    # For the OR-accumulator (return True on hit) the accumulator
    # tracks the HIT, i.e. the invariant's negation -- wrapping
    # without the flip stated found ↔ clean, false at the first hit
    # (measured on the nested-search class, which is the first
    # or-accumulator task whose invariant is the ∀-clean form).
    # Index-bound conjuncts (unquantified) ride OUTSIDE the iff:
    # inside it, `0 <= i < len(l)` would tie the accumulator to list
    # nonemptiness and make the initial invariant unprovable on [].
    conjs = (list(inv_expr.values)
             if isinstance(inv_expr, ast.BoolOp)
             and isinstance(inv_expr.op, ast.And) else [inv_expr])
    quant = [c for c in conjs
             if any(isinstance(nd, ast.Call)
                    and isinstance(nd.func, ast.Name)
                    and nd.func.id in ("all", "any")
                    for nd in ast.walk(c))]
    plain = [c for c in conjs if c not in quant]
    core = (quant[0] if len(quant) == 1
            else ast.BoolOp(op=ast.And(), values=quant) if quant
            else inv_expr)
    lhs: ast.expr = ast.Name(id=acc, ctx=ast.Load())
    neg_wrap_depth = 0
    if hit_ret.value:
        lhs = ast.UnaryOp(op=ast.Not(), operand=lhs)
        # Quantifier depth of the wrapped core: total generators
        # across the nested all-calls (a two-binder clause counts 2).
        neg_wrap_depth = sum(
            len(nd.args[0].generators)
            for nd in ast.walk(core)
            if isinstance(nd, ast.Call)
            and isinstance(nd.func, ast.Name) and nd.func.id == "all"
            and nd.args and isinstance(nd.args[0], ast.GeneratorExp))
    wrapped = ast.Compare(left=lhs, ops=[ast.Eq()],
                          comparators=[core])
    # Plain (unquantified) conjuncts are DROPPED, not carried: they
    # are loop-head guard facts (`0 <= i < len(l)`), structurally
    # true wherever the fold applies its step via the induction's own
    # bounds -- but FALSE at the exit index and on the empty list,
    # where the fold's invariant must still hold. They stay live for
    # the Dafny backend, whose loop-head semantics is where they
    # belong.
    del plain
    ast.copy_location(wrapped, inv_expr)
    ast.fix_missing_locations(wrapped)
    return _LoopShape(index=index, acc=acc,
                      neg_wrap_depth=neg_wrap_depth,
                      init=ast.Constant(value=end_ret.value),
                      start=it.args[0] if len(it.args) == 2 else None,
                      bound=it.args[-1], step=step,
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
    guards: list[tuple[ast.expr, ast.expr]] = field(default_factory=list)
    # `assert` statements between the loop and the return (P2 slice
    # 20). Each is a theorem under the invariant AND the negated
    # condition -- the exit state -- and the proved claim is then
    # substituted into the spec proof. That substitution is what lets
    # the endgame collapse a nonlinear atom like `(i-1)*i` once the
    # exit value of `i` is known: omega cannot multiply, but it can
    # use an equality to rewrite the atom away.
    post_asserts: list[ast.Assert] = field(default_factory=list)


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
    guards, stmts = _split_guards(stmts)
    whiles = [st for st in stmts if isinstance(st, ast.While)]
    if len(whiles) != 1 or any(isinstance(n, ast.While)
                               for st in stmts if st is not whiles[0]
                               for n in ast.walk(st)):
        raise _reject("one `while` loop per function in this slice",
                      whiles[0].lineno if whiles else fn.lineno)
    loop = whiles[0]
    idx = stmts.index(loop)
    inits_stmts, rest = stmts[:idx], stmts[idx + 1:]
    if not inits_stmts or not rest \
            or not isinstance(rest[-1], ast.Return) \
            or not all(isinstance(x, ast.Assert) for x in rest[:-1]):
        raise _reject("a `while` function must be `acc = init` (one or "
                      "more) then `while ...: ...` then optional "
                      "`assert`s then `return expr` in this slice",
                      loop.lineno)
    post_asserts = [x for x in rest[:-1] if isinstance(x, ast.Assert)]
    ret_stmt = rest[-1]
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
    return _WhileShape(guards=guards, post_asserts=post_asserts,
                       accs=accs, inits=inits, cond=loop.test, steps=steps,
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
    guards, stmts = _split_guards(stmts)
    fors = [s for s in stmts if isinstance(s, ast.For)]
    if not fors:
        return None
    if len(fors) > 1:
        raise _reject("one loop per function in this slice", fors[1].lineno)
    early = _early_return_loop(stmts, fn, spec_fn)
    if early is not None:
        early.guards = guards
        return early
    def _is_append(st: ast.stmt) -> bool:
        return (isinstance(st, ast.Expr)
                and isinstance(st.value, ast.Call)
                and isinstance(st.value.func, ast.Attribute)
                and st.value.func.attr == "append"
                and isinstance(st.value.func.value, ast.Name)
                and len(st.value.args) == 1
                and not st.value.keywords)

    post_asserts: list[ast.Assert] = []
    post_appends: list[ast.stmt] = []
    if len(stmts) >= 4 and isinstance(stmts[1], ast.For) \
            and isinstance(stmts[-1], ast.Return) \
            and all(isinstance(x, ast.Assert) or _is_append(x)
                    for x in stmts[2:-1]):
        post_asserts = [x for x in stmts[2:-1]
                        if isinstance(x, ast.Assert)]
        post_appends = [x for x in stmts[2:-1] if _is_append(x)]
        stmts = [stmts[0], stmts[1], stmts[-1]]
    if len(stmts) != 3 or not isinstance(stmts[0], (ast.Assign,
                                                    ast.AnnAssign)) \
            or not isinstance(stmts[1], ast.For) \
            or not isinstance(stmts[2], ast.Return):
        raise _reject("a loop function must be exactly `acc = init; "
                      "for ...: ...: optional `assert`s; return expr` "
                      "(or an early-return search loop) in this slice",
                      fors[0].lineno)
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
            and it.func.id == "range" and len(it.args) in (1, 2)
            and not it.keywords):
        raise _reject("loops must iterate `range(<bound>)` or "
                      "`range(<start>, <bound>)` in this slice "
                      "(a step is not modelled)", loop.lineno)
    start_arg = it.args[0] if len(it.args) == 2 else None
    if loop.orelse:
        raise _reject("`for ... else` is outside the fragment", loop.lineno)
    body = [s for s in loop.body]
    search_test: ast.expr | None = None
    search_hit: bool | None = None
    # Asserts are proof obligations, not steps, so they are lifted out
    # before the shape match and every shape below sees the body it
    # expects. Lifting is exactly what makes POSITION easy to lose,
    # though: the obligation is stated with the loop-HEAD binders and
    # discharged under the loop-HEAD invariant, so it is a claim about
    # the head state. That is the truth only while the accumulator
    # still holds its head value.
    #
    # Measured, before this check existed: `s = s + 1; assert s == i`
    # was certified `ok` even though CPython raises AssertionError on
    # it (the head state satisfies s == i), and the runtime-true
    # `assert s == i + 1` was rejected. Both directions wrong, and the
    # unsound one certifies a program that does not return at all.
    #
    # An assert after the accumulator moves is refused rather than
    # re-positioned: stating it at the right state is a real
    # extension, and guessing is how the above happened.
    def _touches_acc(st: ast.stmt) -> bool:
        for sub in ast.walk(st):
            if isinstance(sub, ast.Name) and sub.id == acc \
                    and isinstance(sub.ctx, ast.Store):
                return True
            # `acc.append(v)` reads the name but mutates the object.
            if isinstance(sub, ast.Call) \
                    and isinstance(sub.func, ast.Attribute) \
                    and isinstance(sub.func.value, ast.Name) \
                    and sub.func.value.id == acc:
                return True
        return False

    body_asserts: list[ast.Assert] = []
    moved = False
    for st in body:
        if isinstance(st, ast.Assert):
            if moved:
                raise _reject(
                    f"an `assert` after the accumulator {acc!r} has "
                    f"been updated is outside this slice — the "
                    f"obligation is discharged under the loop-head "
                    f"invariant, which describes the state BEFORE the "
                    f"update, so proving it there would certify a "
                    f"different claim than the one Python evaluates; "
                    f"move the assert above the update", st.lineno)
            body_asserts.append(st)
        elif _touches_acc(st):
            moved = True
    body = [s for s in body if not isinstance(s, ast.Assert)]
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
    elif len(body) == 2 and isinstance(body[0], ast.Assign) \
            and len(body[0].targets) == 1 \
            and isinstance(body[0].targets[0], ast.Name) \
            and body[0].targets[0].id == acc \
            and isinstance(body[1], ast.If) and not body[1].orelse \
            and len(body[1].body) == 1 \
            and isinstance(body[1].body[0], ast.Return) \
            and isinstance(body[1].body[0].value, ast.Constant) \
            and isinstance(body[1].body[0].value.value, bool):
        # acc-step, then `if TEST: return <bool>` -- the trailing
        # return must be the complement literal (checked below, where
        # ret_stmt is in scope for the search fields).
        step_expr = body[0].value
        search_test = body[1].test
        search_hit = body[1].body[0].value.value
        if not search_hit:
            raise _reject(
                "a search-accumulator loop returns `True` on hit in "
                "this slice — the `return False` pairing inverts the "
                "flag's meaning against the ensures' `exists`",
                body[1].lineno)
        if not (isinstance(ret_stmt.value, ast.Constant)
                and isinstance(ret_stmt.value.value, bool)
                and ret_stmt.value.value == (not search_hit)):
            raise _reject(
                "a search-accumulator loop returns the complement bool "
                "literal after the loop (`if TEST: return True` pairs "
                "with `return False`)", ret_stmt.lineno)
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
    post_append_exprs: list[ast.expr] = []
    for pa in post_appends:
        if pa.value.func.value.id != acc:
            raise _reject(
                f"a trailing append must target the accumulator "
                f"{acc!r} in this slice", pa.lineno)
        if not (isinstance(init_value, ast.List)
                and not init_value.elts):
            raise _reject(
                "a trailing append needs a LIST accumulator in this "
                "slice", pa.lineno)
        for nd in ast.walk(pa.value.args[0]):
            if isinstance(nd, ast.Name) and nd.id in (index, acc):
                raise _reject(
                    f"a trailing append's expression may mention "
                    f"parameters only in this slice — {nd.id!r} is "
                    f"loop state, and the for path has no exit-state "
                    f"machinery", pa.lineno)
        post_append_exprs.append(pa.value.args[0])
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
        for st in body:
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
                      guards=guards, start=start_arg,
                      bound=it.args[-1], step=step_expr,
                      ret=ret_stmt.value, inv=inv_expr, inv_line=inv_line,
                      for_line=loop.lineno, acc_bool=acc_bool,
                      asserts=body_asserts, post_asserts=post_asserts,
                      post_appends=post_append_exprs,
                      search_test=search_test, search_hit=search_hit)


def encode_module_lean(source: str, specs: ModuleSpecs, module_name: str,
                       proof_lemmas: frozenset[str] = frozenset()
                       ) -> LeanEncoded:
    if specs.errors:
        first = specs.errors[0]
        raise EncodeError(f"spec error: {first.error}", first.line)
    # Proof sidecars are live (P3). `proof_lemmas` is the set of names
    # the pack declares, already whitelist-validated by the loader.
    _ABSORBED_INNER_SPANS.clear()
    _FILTER_PREDS.clear()
    _SORTED_UNIQUE_USED.clear()
    module = ast.parse(source)
    # `x += e` is `x = x + e`. Rewriting the whole module once means
    # every path downstream sees a single spelling; desugaring at
    # individual sites left the operator accepted inside a loop body and
    # refused in loop-free code, for no reason a reader could see.
    module = _AugAssignRewriter().visit(module)
    ast.fix_missing_locations(module)
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
                      "len", "sum", "bool", "result", "enumerate",
                      "sorted", "list", "set"):
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
        str_params: set[str] = set()
        for arg in a.args:
            ann = arg.annotation
            if isinstance(ann, ast.Name) and ann.id == "int":
                ptypes[arg.arg] = "Int"
            elif isinstance(ann, ast.Name) and ann.id == "str":
                # Code-point model: a str is its List Int of code
                # points. Sound only under the element discipline
                # checked below — `len` and character-to-character
                # comparisons are exactly the operations Python and
                # the model agree on (Python orders characters by
                # code point).
                ptypes[arg.arg] = "List Int"
                str_params.add(arg.arg)
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
                raise _reject(f"parameter {arg.arg!r} must be `int`, "
                              f"`str`, or `list[int]` in this slice",
                              fn.lineno)
            # No module-wide check for parameters: a binder shadowing a
            # top-level name is legal Lean (and matches Python scoping).
            # The one genuine capture — a parameter named after its OWN
            # function, which the theorem statement must reference beside
            # it — is alpha-renamed in theorem context below.
        if str_params:
            _str_element_discipline(fn, spec_fn, frozenset(str_params))
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
                # Loop-free asserts become their own obligation below,
                # matching Dafny; a `for`-body assert becomes one under
                # the invariant at that iteration (slice 18) and the
                # shape analysis picks it up. What stays out is the
                # assert whose obligation this slice cannot POSITION:
                # under a branch inside the body its claim holds only
                # on that path, and the preservation proof has no
                # hypothesis for the path taken.
                at_for_top = any(
                    node in st.body for st in ast.walk(fn)
                    if isinstance(st, ast.For))
                in_loop = any(
                    node in ast.walk(st)
                    for st in ast.walk(fn)
                    if isinstance(st, (ast.For, ast.While)))
                if in_loop and not at_for_top:
                    raise _reject(
                        "an `assert` nested inside a loop body's branch "
                        "(or in a `while` body) is outside this slice — "
                        "its obligation would have to be discharged "
                        "under the path taken through that iteration, "
                        "which the preservation proof does not carry; "
                        "an assert at the TOP LEVEL of a `for` body is "
                        "admitted", node.lineno)
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
                    and node.func.id == "sorted" \
                    and not _is_sorted_unique_call(node):
                raise _reject(
                    "sorted is outside the Lean slice except as "
                    "`sorted(list(set(L)))` / `sorted(set(L))` (the "
                    "sorted-unique class) — the Dafny backend admits "
                    "list[int] sorted as PySorted (permutation + "
                    "order); bare `sorted` keeps duplicates and "
                    "waits for its own pack", node.lineno)
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
        if is_list_ret and len(params) == 1:
            om = _optional_max_shape(fn, spec_fn, lists0)
            if om is not None:
                # The template's generated declarations join the
                # module-wide reservation set like every other
                # shape's (review-caught: a sibling def named
                # f_loop/f_inv/... would collide silently).
                for g in (f"{spec_fn.name}_loop",
                          f"{spec_fn.name}_inv",
                          f"{spec_fn.name}_loop_inv",
                          f"{spec_fn.name}_assert0"):
                    _check_name(g, "generated declaration for",
                                fn.lineno, taken)
                    taken.add(g)
                _emit_optional_max(om, fn, spec_fn, emit, theorems)
                continue
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
        # Only NOW check `#@ proof` targets. Checking earlier masked the
        # real blocker: a task whose shape this slice does not cover
        # reported "unknown lemma", which reads as "write the pack" when
        # the honest answer is "the fragment does not reach this yet".
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
                    f"target must be declared in the proof sidecar "
                    f"(<stem>.proofs.lean); this one declares "
                    f"{sorted(proof_lemmas) or 'nothing'}", clause.line)
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
                and is_bool != loop.acc_bool \
                and loop.search_test is None:
            # The search-accumulator shape is the one licensed split:
            # an int accumulator with a bool RESULT, because the
            # result is the search flag, not the accumulator.
            raise _reject(
                "a loop function's accumulator must match its return "
                "type in this slice: True/False-initialized accumulators "
                "return `bool`, integer accumulators return `int`",
                fn.lineno)
        if loop is not None and loop.search_test is not None \
                and not is_bool:
            raise _reject(
                "a search-accumulator loop returns `bool` (the early "
                "return is a bool literal)", fn.lineno)
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
            # STRICT. `decreases` is Dafny's TERMINATION MEASURE, not
            # an iteration count: `while i <= n` still runs when the
            # measure `n - i` reaches 0, so the count is `n - i + 1`.
            # Reading the measure as the count made the generated Lean
            # run one iteration short -- a definition that computed
            # sum_to_n(n-1), measured against CPython. With `<`, the
            # zero-fuel case reads "the measure went below its floor",
            # which is exactly the loop having exited.
            emit(f"    {_ident(gen_inv)} {argsp}{avlist} → "
                 f"{_ident(gen_meas)} {argsp}{avlist} < ({fuel} : Int) →",
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
            _wbh, _wbn = _const_div_bridges(fn, spec_fn)
            for _wb in _wbh:
                wdiv_facts.append(f"      {_wb}")
            if _wbn:
                wdiv_facts.append(
                    f"      all_goals (try simp only "
                    f"[{', '.join(_wbn)}] at *)")
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
            # A post-loop `assert` is a claim about the EXIT state:
            # its theorem carries the invariant and the NEGATED
            # condition, which together are everything the loop
            # guarantees on exit. It also carries the `requires` --
            # unlike the induction theorem, it is instantiated in the
            # spec proof, where those are in context to discharge.
            # Positivity for the claim's own divisors comes from the
            # invariant only (cond_lc): the condition is FALSE here,
            # so its facts must not license anything.
            pa_prior: list[str] = []
            for pk, past in enumerate(wloop.post_asserts):
                pa_name = f"{fname}_post_assert{pk}"
                _check_name(pa_name, "generated declaration for",
                            past.lineno, taken)
                taken.add(pa_name)
                _no_old(past.test, past.lineno)
                _reject_undecidable_quantifier(past.test, body_names,
                                               past.lineno, cond_lc)
                pa_claim = _prop_expr(past.test, body_names,
                                      past.lineno, lc=cond_lc)
                pa_hyps = []
                for qi, (qexpr, qline) in enumerate(
                        _parse_clause(spec_fn, "requires")):
                    pa_hyps.append(f"(hq{qi} : "
                                   f"{_prop_expr(qexpr, names, qline, lc=lc0)})")
                pa_hyps.append(f"(hinv : {_ident(gen_inv)} "
                               f"{argsp}{avlist})")
                pa_hyps.append(f"(hcond : {_ident(gen_cond)} "
                               f"{argsp}{avlist} = false)")
                # Dafny proves `assert A; assert B` with A in context
                # for B (the slice-18 lesson, applied at authoring time
                # rather than after review). Sound for the same reason:
                # each claim is discharged by its own theorem, so a
                # false A fails there and takes the file with it.
                pa_hyps.extend(f"(hpp{j} : {c})"
                               for j, c in enumerate(pa_prior))
                emit("", None)
                emit(f"theorem {_ident(pa_name)} {binders} "
                     f"({avlist} : Int)", past.lineno)
                emit(f"    {' '.join(pa_hyps)} :", past.lineno)
                emit(f"    {pa_claim} := by", past.lineno)
                emit(f"  simp only [{_ident(gen_inv)}, "
                     f"{_ident(gen_cond)}, decide_eq_false_iff_not] "
                     f"at hinv hcond", past.lineno)
                for _wb in _wbh:
                    emit(f"  {_wb}", past.lineno)
                if _wbn:
                    emit(f"  all_goals (try simp only "
                         f"[{', '.join(_wbn)}] at *)", past.lineno)
                for tl in ("  all_goals (try push_cast)",
                           "  all_goals (try omega)",
                           "  all_goals (try simp_all)",
                           "  all_goals (first | omega | trivial)"):
                    emit(tl, past.lineno)
                theorems.append(pa_name)
                pa_prior.append(pa_claim)
            emit("", None)
            emit(f"def {_ident(spec_fn.name)} {binders} : Int :=",
                 fn.lineno)
            init_call = (f"{_ident(gen_loop)} {argsp}"
                         f"(({_ident(gen_meas)} {argsp}"
                         + " ".join(f"({t})" for t in init_ts)
                         + ").toNat + 1) "
                         + " ".join(f"({t})" for t in init_ts))
            if nacc == 1:
                ret_t = _int_expr(wloop.ret, body_names, fn.lineno,
                                  lc=lc0)
                # The guards MUST wrap the loop's value here too.
                # Recording them in the shape and then emitting the bare
                # loop modelled a different program from the one Python
                # runs: the guard's early return simply vanished.
                emit("  " + _wrap_guards(
                    wloop.guards,
                    f"let {avs[0]} := {init_call}; {ret_t}",
                    names, fn.lineno, lc0, is_bool, is_list_ret),
                    fn.lineno)
            else:
                if wloop.guards:
                    raise _reject(
                        "a guard before a multi-accumulator `while` is "
                        "outside this slice — the guard would have to "
                        "wrap a multi-line `let` chain", fn.lineno)
                emit(f"  let {pvar} := {init_call}", fn.lineno)
                for k, a in enumerate(avs):
                    emit(f"  let {a} := {pvar}{_proj(k, nacc)}",
                         fn.lineno)
                ret_t = _int_expr(wloop.ret, body_names, fn.lineno,
                                  lc=lc0)
                emit(f"  {ret_t}", fn.lineno)

        elif loop is not None and loop.search_test is not None:
            # The SEARCH-ACCUMULATOR shape (below_zero class): an
            # (Int × Bool) fold. The flag or-tracks the test over the
            # POST-step accumulator; the fold runs to completion and
            # the RESULT is the flag -- identical to the early return
            # because or is monotone and the body is pure. The user's
            # invariants are carried CONDITIONALLY on the flag being
            # false: Dafny owes an invariant only at loop heads the
            # program reaches, and past the hit the real program has
            # returned.
            if loop.guards:
                raise _reject("a guard before a search-accumulator "
                              "loop is outside this slice", fn.lineno)
            if loop.start is not None:
                raise _reject("a search-accumulator loop over "
                              "range(start, bound) is outside this "
                              "slice", loop.for_line)
            for nm, what in ((loop.index, "loop index"),
                             (loop.acc, "accumulator")):
                if nm in params:
                    raise _reject(f"{what} {nm!r} shadows a parameter "
                                  f"— outside this slice",
                                  loop.for_line)
            for sst in loop.asserts:
                for nd in ast.walk(sst.test):
                    if isinstance(nd, ast.Name) and nd.id == loop.acc:
                        raise _reject(
                            "an in-loop `assert` in a search-"
                            "accumulator loop may not mention the "
                            "accumulator in this slice (its obligation "
                            "carries no invariant)", sst.lineno)
            # The flag's meaning comes from the ONE ensures of the
            # licensed form: `result == (exists n in range(bound + 1)
            # :: P)` -- the hit predicate localized to the prefix.
            ens_all = _parse_clause(spec_fn, "ensures")
            syn = None
            for eexpr, eline in ens_all:
                if (isinstance(eexpr, ast.Compare)
                        and len(eexpr.ops) == 1
                        and isinstance(eexpr.ops[0], ast.Eq)
                        and isinstance(eexpr.left, ast.Name)
                        and eexpr.left.id == "result"
                        and isinstance(eexpr.comparators[0], ast.Call)
                        and isinstance(eexpr.comparators[0].func,
                                       ast.Name)
                        and eexpr.comparators[0].func.id == "any"):
                    ecall = eexpr.comparators[0]
                    # Guard the whole dereference chain: `any()`
                    # without a generator, or with the wrong arity,
                    # is simply NOT the licensed form -- it falls to
                    # the reject below with the boundary's message
                    # (review-caught: the raw chain crashed with
                    # IndexError/AttributeError, a tool-error verdict
                    # on a merely-unsupported spec).
                    if not (len(ecall.args) == 1
                            and not ecall.keywords
                            and isinstance(ecall.args[0],
                                           ast.GeneratorExp)
                            and len(ecall.args[0].generators) == 1
                            and not ecall.args[0].generators[0].ifs
                            and isinstance(
                                ecall.args[0].generators[0].iter,
                                ast.Call)):
                        continue
                    gen = ecall.args[0]
                    rng = gen.generators[0].iter
                    if (isinstance(rng, ast.Call) and len(rng.args) == 1
                            and isinstance(rng.args[0], ast.BinOp)
                            and isinstance(rng.args[0].op, ast.Add)
                            and ast.dump(rng.args[0].left)
                            == ast.dump(loop.bound)
                            and isinstance(rng.args[0].right,
                                           ast.Constant)
                            and rng.args[0].right.value == 1):
                        syn = (ecall, eline)
                        break
            if syn is None:
                raise _reject(
                    "a search-accumulator loop needs one ensures of "
                    "the form `result == (exists n in range(<bound> + "
                    "1) :: P)` — the flag's invariant is P localized "
                    "to the processed prefix", fn.lineno)
            syn_call, syn_line = syn
            # SYNTH(i): the same ∃ with the range hi replaced by i+1.
            loc_call = copy.deepcopy(syn_call)
            loc_call.args[0].generators[0].iter.args[0] = ast.BinOp(
                left=ast.Name(id=loop.index, ctx=ast.Load()),
                op=ast.Add(), right=ast.Constant(value=1))
            ast.fix_missing_locations(loc_call)
            fname = spec_fn.name
            gen_loop, gen_inv, gen_thm = (f"{fname}_loop",
                                          f"{fname}_inv",
                                          f"{fname}_loop_inv")
            for g in (gen_loop, gen_inv, gen_thm):
                _check_name(g, "generated declaration for", fn.lineno,
                            taken)
                taken.add(g)
            body_names = names | {loop.index, loop.acc}
            args = " ".join(_ident(pn) for pn in params)
            argsp = (args + " ") if args else ""
            used_plain = set(params) | {loop.index, loop.acc}
            fuel = "m"
            while fuel in used_plain:
                fuel += "'"
            kvar = "k"
            while kvar in used_plain or kvar == fuel:
                kvar += "'"
            fvar = "f_"
            while fvar in used_plain or fvar in (fuel, kvar):
                fvar += "'"
            iv, av = _ident(loop.index), _ident(loop.acc)
            safe = {loop.index: loop.bound.args[0].id
                    if (isinstance(loop.bound, ast.Call)
                        and isinstance(loop.bound.func, ast.Name)
                        and loop.bound.func.id == "len"
                        and loop.bound.args
                        and isinstance(loop.bound.args[0], ast.Name)
                        and loop.bound.args[0].id in lc0.lists)
                    else "*"}
            if safe[loop.index] == "*":
                safe = {}
            step_lc = _ListCtx(lc0.lists, safe, None,
                               min_len=lc0.min_len,
                               pos_names=lc0.pos_names,
                               nonneg_names=lc0.nonneg_names)
            inv_lc = _ListCtx(lc0.lists, dict(safe), loop.index,
                              scaffold=True, min_len=lc0.min_len,
                              pos_names=lc0.pos_names,
                              nonneg_names=lc0.nonneg_names)
            bound_t = _int_expr(loop.bound, names, fn.lineno, lc=lc0)
            init_t = _int_expr(loop.init, names, fn.lineno, lc=lc0)
            step_t = _int_expr(loop.step, body_names, loop.for_line,
                               lc=step_lc)
            # TEST over the POST-step accumulator: substitute the step
            # into the test before translating.
            test_post = _SubstExprs(
                {loop.acc: copy.deepcopy(loop.step)}).visit(
                copy.deepcopy(loop.search_test))
            test_t = _prop_expr(test_post, body_names, loop.for_line,
                                lc=step_lc)
            inv_user = _prop_expr(loop.inv, body_names, loop.inv_line,
                                  lc=inv_lc)
            synth_t = _prop_expr(loc_call, body_names, syn_line,
                                 lc=inv_lc)
            hit_lit = "true" if loop.search_hit else "false"
            miss_lit = "false" if loop.search_hit else "true"
            emit("", None)
            emit(f"def {_ident(gen_loop)} {binders} : "
                 f"Nat → Int → Int → Bool → Int × Bool",
                 loop.for_line)
            emit(f"  | 0, _, {av}, {fvar} => ({av}, {fvar})",
                 loop.for_line)
            emit(f"  | ({fuel} + 1), {iv}, {av}, {fvar} => "
                 f"{_ident(gen_loop)} {argsp}{fuel} ({iv} + 1) "
                 f"({step_t}) ({fvar} || decide {test_t})",
                 loop.for_line)
            emit("", None)
            emit(f"def {_ident(gen_inv)} {binders} ({iv} : Int) "
                 f"({av} : Int) ({fvar} : Bool) : Prop :=",
                 loop.inv_line)
            emit(f"  (({fvar} = false) → {inv_user}) ∧ "
                 f"(({fvar} = true) ↔ {synth_t})", loop.inv_line)
            # In-loop asserts: obligations over params + index only
            # (checked above), so no invariant hypothesis is needed.
            sa_facts: list[str] = []
            for si, sst in enumerate(loop.asserts):
                a_name = f"{fname}_loop_assert{si}"
                _check_name(a_name, "generated declaration for",
                            sst.lineno, taken)
                taken.add(a_name)
                _no_old(sst.test, sst.lineno)
                claim_lc = _ListCtx(step_lc.lists, step_lc.safe_idx,
                                    loop.index, step_lc.scaffold,
                                    step_lc.min_len,
                                    step_lc.pos_names,
                                    step_lc.result_list,
                                    step_lc.result_is_list,
                                    step_lc.nonneg_names)
                _reject_undecidable_quantifier(sst.test, body_names,
                                               sst.lineno, claim_lc)
                sa_claim = _prop_expr(sst.test, body_names, sst.lineno,
                                      lc=claim_lc)
                emit("", None)
                emit(f"theorem {_ident(a_name)} {binders} "
                     f"({iv} : Int)", sst.lineno)
                emit(f"    (hlo : 0 ≤ {iv}) (hhi : {iv} < {bound_t}) :",
                     sst.lineno)
                emit(f"    {sa_claim} := by", sst.lineno)
                ext = _slice_extension_shape(sst.test, loop.index,
                                             claim_lc, body_names)
                if ext is not None:
                    xlist, xfn = ext
                    xcall = (f"VeriPy.Take_succ_getD {xlist}"
                             if xfn is None else
                             f"VeriPy.Map_take_succ {xfn} {xlist}")
                    emit(f"  all_goals (try (rw [show (({iv}) + "
                         f"1).toNat = ({iv}).toNat + 1 from by omega]; "
                         f"exact {xcall} ({iv}).toNat (by omega)))",
                         sst.lineno)
                for tl in ("  all_goals (try simp_all)",
                           "  all_goals (first | omega | trivial)"):
                    emit(tl, sst.lineno)
                theorems.append(a_name)
                sa_facts.append(
                    f"      have hla{si} := {_ident(a_name)} "
                    f"{argsp}{iv} hi (by omega)")
            emit("", None)
            app_pair = f"({_ident(gen_loop)} {argsp}{fuel} {iv} {av} {fvar})"
            emit(f"theorem {_ident(gen_thm)} {binders} : "
                 f"∀ ({fuel} : Nat) ({iv} {av} : Int) "
                 f"({fvar} : Bool),", loop.inv_line)
            emit(f"    {_ident(gen_inv)} {argsp}{iv} {av} {fvar} → "
                 f"0 ≤ {iv} → {iv} + ({fuel} : Int) ≤ {bound_t} →",
                 loop.inv_line)
            emit(f"    {_ident(gen_inv)} {argsp}({iv} + {fuel}) "
                 f"{app_pair}.1 {app_pair}.2 := by", loop.inv_line)
            emit(f"  intro {fuel}", loop.inv_line)
            emit(f"  induction {fuel} with", loop.inv_line)
            emit("  | zero =>", loop.inv_line)
            emit(f"      intro {iv} {av} {fvar} h hi hb",
                 loop.inv_line)
            emit(f"      simp only [{_ident(gen_loop)}]",
                 loop.inv_line)
            emit(f"      simpa using h", loop.inv_line)
            emit(f"  | succ {kvar} ih =>", loop.inv_line)
            emit(f"      intro {iv} {av} {fvar} h hi hb",
                 loop.inv_line)
            emit(f"      simp only [{_ident(gen_loop)}]",
                 loop.inv_line)
            for fact in sa_facts:
                emit(fact, loop.inv_line)
            emit(f"      have hstep := ih ({iv} + 1) ({step_t}) "
                 f"({fvar} || decide {test_t})", loop.inv_line)
            # Arity of the user invariant's conjunction, for the
            # destructure and the goal split.
            n_conj = (len(loop.inv.values)
                      if isinstance(loop.inv, ast.BoolOp)
                      and isinstance(loop.inv.op, ast.And) else 1)
            hues = ", ".join(f"hue{j}_" for j in range(n_conj))
            holes = ", ".join("?_" for _ in range(n_conj))
            list_arg = (sorted(lc0.lists)[0] if lc0.lists else None)
            emit("        (by", loop.inv_line)
            emit(f"          simp only [{_ident(gen_inv)}] at h ⊢",
                 loop.inv_line)
            emit("          obtain ⟨hu_, hiff_⟩ := h", loop.inv_line)
            if list_arg is not None:
                emit(f"          have hsum_ := VeriPy.PySum_take_succ "
                     f"{_ident(list_arg)} ({iv}).toNat", loop.inv_line)
                # The prelude states sums over List.getD; the step
                # translation indexes as `xs[i]?.getD`. One unfold
                # aligns the atoms -- without it, omega holds two
                # names for the same element and closes nothing.
                emit("          all_goals (try simp only [List.getD] "
                     "at hsum_)", loop.inv_line)
            emit("          constructor", loop.inv_line)
            emit("          · intro hf_", loop.inv_line)
            emit("            simp only [Bool.or_eq_false_iff, "
                 "decide_eq_false_iff_not] at hf_", loop.inv_line)
            emit("            have hu2_ := hu_ hf_.1", loop.inv_line)
            if n_conj > 1:
                emit(f"            obtain ⟨{hues}⟩ := hu2_",
                     loop.inv_line)
            emit(f"            all_goals (try (rw [show (({iv}) + "
                 f"1).toNat = ({iv}).toNat + 1 from by omega] at *))",
                 loop.inv_line)
            if n_conj > 1:
                emit(f"            refine ⟨{holes}⟩", loop.inv_line)
            hue_conj = " | ".join(
                [f"(exact hue{j}_ nq_ ⟨hq0_, hlt_⟩)"
                 for j in range(n_conj)] + ["simp_all", "omega"])
            hue_curr = " | ".join(
                [f"(exact hue{j}_ nq_ hq0_ hlt_)"
                 for j in range(n_conj)] + ["simp_all", "omega"])
            ge_tail = [
                "                     rw [hne2_]",
                "                     rw [show "
                f"(({iv}) + 1).toNat = ({iv}).toNat + 1 from by "
                "omega]",
                "                     all_goals (try (rw [hla0]))",
                "                     all_goals (try (rw [hsum_]))",
                "                     all_goals (try simp_all)",
                "                     all_goals (first | omega "
                "| trivial))",
            ]
            for _b in range(max(n_conj, 1)):
                pre = "            · " if n_conj > 1 else "            "
                emit(pre + "first", loop.inv_line)
                emit("                | omega", loop.inv_line)
                # The user quantifier's bound is emitted CONJUNCTIVE
                # (`(lo ≤ n ∧ n < hi) → P`), and simp sometimes
                # curries it before this script runs -- so both intro
                # shapes are alternatives, in that order (measured:
                # a three-binder intro on the conjunctive form fails
                # introN and the whole alternative silently rolled
                # back inside `first`).
                emit("                | (intro nq_ hqq_",
                     loop.inv_line)
                emit("                   obtain ⟨hq0_, hq1_⟩ := hqq_",
                     loop.inv_line)
                emit("                   rcases Classical.em "
                     f"(nq_ < {iv} + 1) with hlt_ | hge_",
                     loop.inv_line)
                emit(f"                   · first | {hue_conj}",
                     loop.inv_line)
                emit("                   · have hne2_ : nq_ = "
                     f"{iv} + 1 := by omega", loop.inv_line)
                for tl in ge_tail:
                    emit(tl, loop.inv_line)
                emit("                | (intro nq_ hq0_ hq1_",
                     loop.inv_line)
                emit("                   rcases Classical.em "
                     f"(nq_ < {iv} + 1) with hlt_ | hge_",
                     loop.inv_line)
                emit(f"                   · first | {hue_curr}",
                     loop.inv_line)
                emit("                   · have hne2_ : nq_ = "
                     f"{iv} + 1 := by omega", loop.inv_line)
                for tl in ge_tail:
                    emit(tl, loop.inv_line)
                emit("                | simp_all", loop.inv_line)
                emit("                | trivial", loop.inv_line)
            emit("          · simp only [Bool.or_eq_true, "
                 "decide_eq_true_eq]", loop.inv_line)
            emit("            constructor", loop.inv_line)
            emit("            · intro hor_", loop.inv_line)
            emit(f"              by_cases hfv_ : {fvar} = true",
                 loop.inv_line)
            emit("              · obtain ⟨n_, hn_, hp_⟩ := "
                 "hiff_.mp hfv_", loop.inv_line)
            emit("                exact ⟨n_, ⟨hn_.1, by omega⟩, hp_⟩",
                 loop.inv_line)
            emit("              · rcases hor_ with hfv2_ | ht2_",
                 loop.inv_line)
            emit("                · exact absurd hfv2_ hfv_",
                 loop.inv_line)
            emit(f"                · refine ⟨{iv} + 1, "
                 f"⟨by omega, by omega⟩, ?_⟩", loop.inv_line)
            emit("                  have hu2_ := hu_ (by "
                 "simpa using hfv_)", loop.inv_line)
            emit("                  all_goals (try (rw [show "
                 f"(({iv}) + 1).toNat = ({iv}).toNat + 1 from by "
                 "omega] at *))", loop.inv_line)
            emit("                  all_goals (try simp_all)",
                 loop.inv_line)
            emit("                  all_goals (try omega)",
                 loop.inv_line)
            emit("                  all_goals (first | omega | "
                 "trivial)", loop.inv_line)
            emit("            · intro hex_", loop.inv_line)
            emit("              obtain ⟨n_, hn_, hp_⟩ := hex_",
                 loop.inv_line)
            emit(f"              by_cases hnl_ : n_ < {iv} + 1",
                 loop.inv_line)
            emit("              · left", loop.inv_line)
            emit("                exact hiff_.mpr ⟨n_, ⟨hn_.1, "
                 "hnl_⟩, hp_⟩", loop.inv_line)
            emit(f"              · by_cases hfv_ : {fvar} = true",
                 loop.inv_line)
            emit("                · simp [hfv_]", loop.inv_line)
            emit("                · right", loop.inv_line)
            emit(f"                  have hne_ : n_ = {iv} + 1 := "
                 "by omega", loop.inv_line)
            emit("                  rw [hne_] at hp_", loop.inv_line)
            emit("                  have hu2_ := hu_ (by "
                 "simpa using hfv_)", loop.inv_line)
            emit("                  all_goals (try (rw [show "
                 f"(({iv}) + 1).toNat = ({iv}).toNat + 1 from by "
                 "omega] at *))", loop.inv_line)
            emit("                  all_goals (try simp_all)",
                 loop.inv_line)
            emit("                  all_goals (try omega)",
                 loop.inv_line)
            emit("                  all_goals (first | omega | "
                 "trivial)", loop.inv_line)
            emit("        )", loop.inv_line)
            emit("        (by omega) (by (try push_cast at hb ⊢); "
                 "omega)", loop.inv_line)
            emit(f"      simp only [{_ident(gen_inv)}] at hstep ⊢",
                 loop.inv_line)
            emit(f"      all_goals (try push_cast at hstep ⊢)",
                 loop.inv_line)
            emit(f"      all_goals (try (rw [show ({iv} + 1 + "
                 f"({kvar} : Int)) = ({iv} + (({kvar} : Int) + 1)) "
                 f"from by omega] at hstep))", loop.inv_line)
            emit("      all_goals (try (exact hstep))", loop.inv_line)
            emit("      all_goals (try simp_all)", loop.inv_line)
            emit("      all_goals (first | omega | trivial)",
                 loop.inv_line)
            emit("", None)
            emit(f"def {_ident(spec_fn.name)} {binders} : Bool :=",
                 fn.lineno)
            pair_call = (f"({_ident(gen_loop)} {argsp}"
                         f"({bound_t}).toNat 0 ({init_t}) false).2")
            # `return True` on hit: the result IS the flag. `return
            # False` on hit: the result is its negation.
            emit(f"  {pair_call}" if loop.search_hit
                 else f"  (!{pair_call})", fn.lineno)
            theorems.append(gen_thm)

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
            # `len(L)` licenses the index for L, and so does
            # `len(L) - k` for a nonnegative literal k: the index only
            # gets SMALLER (intersperse loops to len - 1).
            if isinstance(b, ast.BinOp) and isinstance(b.op, ast.Sub) \
                    and isinstance(b.right, ast.Constant) \
                    and isinstance(b.right.value, int) \
                    and not isinstance(b.right.value, bool) \
                    and b.right.value >= 0:
                b = b.left
            safe: dict[str, str] = {}
            if isinstance(b, ast.Call) and isinstance(b.func, ast.Name) \
                    and b.func.id == "len" and not b.keywords \
                    and len(b.args) == 1 \
                    and isinstance(b.args[0], ast.Name) \
                    and b.args[0].id in lc0.lists:
                safe[loop.index] = b.args[0].id
            # The index is NONNEGATIVE wherever the body runs when the
            # start is (a 1-arg range starts at zero) -- which is what
            # lets a flattened inner window `range(i + 1, len(l))`
            # license its own reads.
            step_nonneg = (frozenset(lc0.nonneg_names | {loop.index})
                           if (loop.start is None
                               or _nonneg_bound(loop.start, lc0))
                           else lc0.nonneg_names)
            step_lc = _ListCtx(lc0.lists, safe, None,
                               min_len=lc0.min_len,
                               pos_names=lc0.pos_names,
                               nonneg_names=step_nonneg)
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
            start_t = ("0" if loop.start is None
                       else _int_expr(loop.start, names, fn.lineno,
                                      lc=lc0))
            # A positive-LITERAL start makes the index positive at
            # every index CPython evaluates the body at, which is what
            # licenses `n % k` in an is_prime-shaped step. The generated
            # fold is total beyond that range, but it is only ever
            # APPLIED at (start, fuel) matching CPython's iterations, so
            # the divisor obligation is discharged where it matters.
            #
            # Literal ONLY -- measured, not a style choice. A SYMBOLIC
            # start positive by `requires` licenses the translation just
            # as soundly (Python cannot divide by zero at runtime), but
            # the induction theorem does not carry the function's
            # requires, so the start's positivity is unprovable exactly
            # where the licensed expression lands and a correct program
            # earned a `failed` verdict -- a false-spec claim, the worst
            # verdict short of unsoundness. _positive_bound accepts
            # such names, so it is deliberately NOT used here. Until
            # the theorems carry a start-positivity premise, refusing
            # at encode time is the honest verdict.
            start_lit = (loop.start.value if loop.start is not None
                         and isinstance(loop.start, ast.Constant)
                         and isinstance(loop.start.value, int)
                         and not isinstance(loop.start.value, bool)
                         else None)
            if start_lit is not None and start_lit >= 1:
                step_lc = _ListCtx(step_lc.lists, step_lc.safe_idx,
                                   step_lc.take_idx, step_lc.scaffold,
                                   step_lc.min_len,
                                   frozenset(step_lc.pos_names
                                             | {loop.index}),
                                   step_lc.result_list,
                                   step_lc.result_is_list,
                                   frozenset(step_lc.nonneg_names
                                             | {loop.index}))
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
            # An `assert` in the loop body, read exactly as Dafny
            # reads it: PROVE, then assume. The proof is its own
            # theorem under the invariant at that iteration plus the
            # index bounds that hold wherever the body runs; the
            # assumption is a `have` in the preservation step below.
            # Only the proved form is ever assumed, so the hint cannot
            # smuggle in a fact the prover has not earned.
            #
            # Like the induction theorem itself, this carries the
            # invariant and the bounds but NOT the function's
            # `requires` -- there is nothing at the injection site to
            # discharge them with. Honest incompleteness: an assert
            # that needs a precondition is refused, not assumed.
            assert_facts: list[str] = []
            # Dafny proves `assert A; assert B` with A IN CONTEXT for
            # B, so each obligation here carries the ones before it.
            # Sound because every one of them is discharged by its own
            # theorem under the same hypotheses -- a false A fails on
            # its own and takes the file with it, so it can never be
            # the thing that lets B through.
            prior: list[tuple[str, str]] = []
            for si, sst in enumerate(loop.asserts):
                a_name = f"{fname}_loop_assert{si}"
                _check_name(a_name, "generated declaration for",
                            sst.lineno, taken)
                taken.add(a_name)
                _no_old(sst.test, sst.lineno)
                # The claim's slice bounds are the loop index (and
                # index-plus-literal), so its context carries take_idx
                # -- step_lc does not, since executable code has no
                # business taking prefixes.
                claim_lc = _ListCtx(step_lc.lists, step_lc.safe_idx,
                                    loop.index, step_lc.scaffold,
                                    step_lc.min_len, step_lc.pos_names,
                                    step_lc.result_list,
                                    step_lc.result_is_list,
                                    step_lc.nonneg_names)
                _reject_undecidable_quantifier(sst.test, body_names,
                                               sst.lineno, claim_lc)
                claim_t = _prop_expr(sst.test, body_names, sst.lineno,
                                     lc=claim_lc)
                emit(f"theorem {_ident(a_name)} {binders} "
                     f"({iv} : Int) ({av} : {acc_ty})", sst.lineno)
                hyps = (f"(hinv : {_ident(gen_inv)} {argsp}{iv} {av}) "
                        f"(hlo : {start_t} ≤ {iv}) "
                        f"(hhi : {iv} < {bound_t})"
                        + "".join(f" ({hn} : {hc})" for hn, hc in prior))
                emit(f"    {hyps} :", sst.lineno)
                emit(f"    {claim_t} := by", sst.lineno)
                # The slice-extension idiom -- the corpus's standing
                # proof hint, `[f(x) for x in xs[:i+1]] == [f(x) for x
                # in xs[:i]] + [f(xs[i])]` -- is Map_take_succ applied
                # at the index, with the bound discharged from the
                # obligation's own `i < len` hypothesis. Detected by
                # shape and closed by `exact`: the lemma's `f (getD i)`
                # and the claim's spelled-out element are beta-defeq.
                ext = _slice_extension_shape(sst.test, loop.index,
                                             claim_lc, body_names)
                if ext is not None:
                    xlist, xfn = ext
                    xcall = (f"VeriPy.Take_succ_getD {xlist}"
                             if xfn is None else
                             f"VeriPy.Map_take_succ {xfn} {xlist}")
                    emit(f"  all_goals (try (rw [show (({_ident(loop.index)}) + 1).toNat "
                         f"= ({_ident(loop.index)}).toNat + 1 from by "
                         f"omega]; exact {xcall} "
                         f"({_ident(loop.index)}).toNat "
                         f"(by omega)))", sst.lineno)
                for tl in ("  all_goals (simp only [" + _ident(gen_inv)
                           + "] at hinv)",
                           "  try simp only [decide_eq_true_eq] at *",
                           "  repeat' split",
                           "  all_goals (try intros)",
                           "  all_goals (try simp_all)",
                           "  all_goals (try omega)",
                           "  all_goals (first | omega | trivial)"):
                    emit(tl, sst.lineno)
                emit("", None)
                theorems.append(a_name)
                assert_facts.append(
                    f"      have hla{si} := {_ident(a_name)} "
                    f"{argsp}{iv} {av} h hi (by omega)"
                    + "".join(f" {hn}" for hn, _ in prior))
                prior.append((f"hla{si}", claim_t))
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
            # `max` covers the EMPTY range: instantiated at the start
            # index with fuel (bound - start).toNat, the plain bound
            # form is FALSE whenever bound < start (range(2, 1) is
            # is_prime(2)), and the spec proof could not begin. With
            # max the hypothesis is true with zero fuel there, and for
            # any positive fuel omega recovers `i + fuel ≤ bound` from
            # it, so the preservation cases keep their full strength.
            # `start ≤ i`, not `0 ≤ i`: the fold is only ever applied
            # from the start index, and the preservation VC below the
            # start can be genuinely FALSE -- is_prime's step conjunct
            # `n % i != 0` fails at i=1 while the empty-domain
            # invariant holds, so a theorem quantifying over i=1 would
            # be unprovable for a correct program.
            emit(f"    {_ident(gen_inv)} {argsp}{iv} {av} → "
                 f"{start_t} ≤ {iv} → "
                 f"{iv} + ({fuel} : Int) ≤ max ({bound_t}) {iv} →",
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
            # The mapped-fold alternative is EXPENSIVE (simp_all
            # over the whole context) and fires only when the
            # invariant actually folds a mapped sum -- unconditional,
            # it multiplied the suite's runtime several-fold, timing
            # out a run that normally takes ninety seconds.
            has_mapped_sum = any(
                isinstance(nd, ast.Call)
                and isinstance(nd.func, ast.Name)
                and nd.func.id == "sum" and nd.args
                and isinstance(nd.args[0], ast.GeneratorExp)
                for nd in ast.walk(loop.inv))
            mapped_alt = (
                f" | ((try simp only [show ({iv} + 1).toNat = "
                f"({iv}).toNat + 1 from by omega] at *); "
                f"simp_all [VeriPy.PySum_append_one]; try omega)"
                if has_mapped_sum else "")
            # The PARITY class (intersperse): a list accumulator whose
            # elementwise invariants read through `% 2`-style mod.
            # Every appended element is one seam; old indices route
            # through GetD_append_left (once per append), each seam
            # through GetD_append_left for the outer appends then
            # GetD_append_last, and the LENGTH conjunct identifies the
            # seams arithmetically. Rather than scripting the seam
            # case-split per index, the alternative hands simp_all the
            # seam equations as HAVES and lets the mod bridges close
            # the parity residues.
            has_parity = (loop.acc_list
                          and isinstance(loop.step, ast.Tuple)
                          and any(isinstance(nd, ast.BinOp)
                                  and isinstance(nd.op, ast.Mod)
                                  for nd in ast.walk(loop.inv)))
            emit(f"  | succ {kvar} ih =>", loop.inv_line)
            emit(f"      intro {iv} {av} h hi hb", loop.inv_line)
            emit(f"      simp only [{_ident(gen_loop)}]", loop.inv_line)
            for fact in div_facts:
                emit(fact, loop.inv_line)
            # Before anything unfolds `h`: the obligation theorem wants
            # the invariant in its FOLDED form, and the surrounding
            # `simp only [...] at *` further down would have rewritten
            # it out from under the application.
            for fact in assert_facts:
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
            elif has_parity:
                # The PARITY class (intersperse): elementwise
                # invariants read through constant-mod, and every
                # appended element is one SEAM. Old indices route
                # through GetD_append_left once per append level; each
                # seam rewrites its position to the prefix length and
                # closes by GetD_append_last, with the constant-div
                # bridges turning the parity residues linear. The
                # script is the scratch-proven probe, generalized over
                # the append count and the invariant's arity.
                napp = len(loop.step.elts)
                n_conj_p = (len(loop.inv.values)
                            if isinstance(loop.inv, ast.BoolOp)
                            and isinstance(loop.inv.op, ast.And) else 1)
                pj = ", ".join(f"hj{ci}_" for ci in range(n_conj_p))
                ph = ", ".join("?_" for _ in range(n_conj_p))
                inst = " | ".join(
                    [f"(exact hj{ci}_ k_ ⟨hk_.1, by omega⟩)"
                     for ci in range(n_conj_p)]
                    + [f"(exact hj{ci}_ k_ hk_.1 (by omega))"
                       for ci in range(n_conj_p)]
                    + ["trivial"])
                pbr_h, pbr_n = _const_div_bridges(fn, spec_fn)
                left_chain = ", ".join(
                    ["VeriPy.GetD_append_left _ _ _ (by "
                     "simp [List.length_append]; try omega)"] * (napp - 1)
                    + ["VeriPy.GetD_append_left _ _ _ hin_"])
                for tl in (
                    "        (by",
                    f"          simp only [{_ident(gen_inv)}] at h ⊢",
                    *(f"          {h_}" for h_ in pbr_h),
                    f"          (try (obtain ⟨{pj}⟩ := h))",
                    f"          refine ⟨{ph}⟩ <;>",
                    "          first",
                    "            | (simp [List.length_append]; "
                    "all_goals omega)",
                    "            | (intro k_ hk_",
                    "               simp only [List.length_append, "
                    "List.length_cons, List.length_nil] at hk_",
                    "               rcases Classical.em ((k_).toNat "
                    f"< {av}.length) with hin_ | hout_",
                    f"               · rw [{left_chain}]",
                    f"                 first | {inst}",
                ):
                    emit(tl, loop.inv_line)
                for j in range(napp):
                    outer = ", ".join(
                        ["VeriPy.GetD_append_left _ _ _ (by "
                         "simp [List.length_append]; try omega)"]
                        * (napp - 1 - j))
                    lead = ("               · " if j == 0
                            else "                 · ")
                    if j < napp - 1:
                        emit(f"{lead}rcases Classical.em ((k_).toNat "
                             f"= {av}.length + {j}) with hs{j}_ | "
                             f"hsn{j}_", loop.inv_line)
                        body_lead = "                 "
                        seam_pos = (f"{av}.length + {j}" if j
                                    else f"{av}.length")
                        emit(f"{body_lead}· "
                             + (f"rw [{outer}]; " if outer else "")
                             + f"rw [show (k_).toNat = "
                             f"{seam_pos} from by omega]",
                             loop.inv_line)
                    else:
                        seam_pos = (f"{av}.length + {j}" if j
                                    else f"{av}.length")
                        emit(f"{lead}"
                             + (f"rw [{outer}]; " if outer else "")
                             + f"rw [show (k_).toNat = "
                             f"{seam_pos} from by omega]",
                             loop.inv_line)
                        body_lead = "                 "
                    ind = "                   "
                    if j > 0:
                        pref_terms = " ++ ".join(
                            "[" + _int_expr(loop.step.elts[q],
                                            body_names, loop.for_line,
                                            lc=step_lc) + "]"
                            for q in range(j))
                        emit(f"{ind}rw [show ({av}.length + {j}) = "
                             f"({av} ++ {pref_terms}).length from by "
                             f"simp [List.length_append]; try omega]",
                             loop.inv_line)
                    emit(f"{ind}rw [VeriPy.GetD_append_last]",
                         loop.inv_line)
                    if pbr_n:
                        emit(f"{ind}(try simp only "
                             f"[{', '.join(pbr_n)}] at *)",
                             loop.inv_line)
                    emit(f"{ind}(try (have hdiv_ : k_ / 2 = {iv} "
                         f":= by omega)); (try rw [hdiv_])",
                         loop.inv_line)
                    emit(f"{ind}all_goals (first | rfl | trivial | "
                         f"omega | (left; omega) | (right; first | "
                         f"rfl | trivial | omega))", loop.inv_line)
                emit("            )", loop.inv_line)
                emit("        )", loop.inv_line)
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
                     f"simp only [VeriPy.PySum_take_succ]; omega)"
                     + mapped_alt + ")",
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
            elif loop.neg_wrap_depth >= 2:
                # The NESTED-SEARCH preservation (scratch-proven, then
                # depth-parameterized): the ¬-wrapped ∀-chain extends
                # by one outer index, whose fresh slice is exactly the
                # flattened inner ∃'s negation.
                D = loop.neg_wrap_depth
                intro_chain = " ".join(
                    f"a{k}_ ha{k}_" for k in range(1, D + 1))
                apply_rest = " ".join(
                    f"a{k}_ ha{k}_" for k in range(2, D + 1))
                wit = "heq_"
                for k in range(D, 1, -1):
                    wit = (f"⟨a{k}_, ha{k}_, {wit}⟩")
                for tl in (
                    "        (by",
                    f"          simp only [{_ident(gen_inv)}, "
                    f"Bool.or_eq_true, decide_eq_true_eq, not_or] "
                    f"at h ⊢",
                    "          first",
                    "          | omega",
                    "          | (constructor",
                    f"             · rintro ⟨hb_, hnex_⟩ "
                    f"{intro_chain} heq_",
                    f"               rcases Classical.em "
                    f"(a1_ < {iv}) with hlt_ | hge_",
                    f"               · exact h.mp hb_ a1_ "
                    f"⟨ha1_.1, hlt_⟩ {apply_rest} heq_",
                    f"               · have hae_ : a1_ = {iv} := "
                    f"by omega",
                    "                 subst hae_",
                    f"                 exact hnex_ {wit}",
                    "             · intro hall_",
                    f"               refine ⟨h.mpr (fun {intro_chain} "
                    f"=> hall_ a1_ ⟨ha1_.1, by omega⟩ "
                    f"{apply_rest}), ?_⟩",
                    f"               rintro {wit}",
                    f"               exact hall_ {iv} ⟨hi, by omega⟩ "
                    f"{apply_rest} heq_))",
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
            # Trailing asserts: parameters-only claims (the for path
            # has no exit-state machinery -- that is the while
            # path's), each a theorem under the requires. take_length
            # sits in the ladder because the corpus's trailing assert
            # is exactly the take-to-whole-list collapse.
            for pk, past in enumerate(loop.post_asserts):
                # LEXICALLY SCOPED, not by spelling: a binder named
                # like the index shadows it only inside its own
                # comprehension (and, per Python, NOT in the first
                # generator's iterable, which evaluates in enclosing
                # scope). A spelling-based exemption let a free
                # occurrence outside the comprehension fall through to
                # the generic unknown-name message — refused either
                # way (loop state can never be a parameter), but the
                # boundary should speak with its own voice.
                def _no_loop_state(e: ast.expr, bound: frozenset[str],
                                   _line: int) -> None:
                    if isinstance(e, ast.Name):
                        if e.id in (loop.index, loop.acc) \
                                and e.id not in bound:
                            raise _reject(
                                f"a post-loop `assert` on a `for` may "
                                f"mention parameters only in this "
                                f"slice — {e.id!r} is loop state, and "
                                f"the for path has no exit-state "
                                f"machinery (a `while` does)", _line)
                        return
                    if isinstance(e, (ast.ListComp, ast.SetComp,
                                      ast.GeneratorExp)):
                        b = set(bound)
                        for gi, g in enumerate(e.generators):
                            _no_loop_state(g.iter,
                                           frozenset(b) if gi
                                           else bound, _line)
                            if isinstance(g.target, ast.Name):
                                b.add(g.target.id)
                            for c in g.ifs:
                                _no_loop_state(c, frozenset(b), _line)
                        _no_loop_state(e.elt, frozenset(b), _line)
                        return
                    for child in ast.iter_child_nodes(e):
                        if isinstance(child, ast.expr):
                            _no_loop_state(child, bound, _line)
                _no_loop_state(past.test, frozenset(), past.lineno)
                pa_name = f"{fname}_post_assert{pk}"
                _check_name(pa_name, "generated declaration for",
                            past.lineno, taken)
                taken.add(pa_name)
                _no_old(past.test, past.lineno)
                _reject_undecidable_quantifier(past.test, names,
                                               past.lineno, lc0)
                pa_claim = _prop_expr(past.test, names, past.lineno,
                                      lc=lc0)
                pa_hyps = []
                for qi, (qexpr, qline) in enumerate(
                        _parse_clause(spec_fn, "requires")):
                    pa_hyps.append(f"(hq{qi} : "
                                   f"{_prop_expr(qexpr, names, qline, lc=lc0)})")
                emit("", None)
                emit(f"theorem {_ident(pa_name)} {binders}"
                     + ("" if not pa_hyps else " " + " ".join(pa_hyps))
                     + " :", past.lineno)
                emit(f"    {pa_claim} := by", past.lineno)
                for tl in ("  all_goals (try simp only "
                           "[Int.toNat_natCast, List.take_length])",
                           "  all_goals (try simp_all)",
                           "  all_goals (first | rfl | omega | trivial)"):
                    emit(tl, past.lineno)
                theorems.append(pa_name)
            ret_t = av if (loop.acc_bool or loop.acc_list) \
                else _int_expr(loop.ret, names | {loop.acc}, fn.lineno,
                               lc=lc0)
            # Trailing appends concatenate after the fold. Their
            # expressions translate under GUARD-DERIVED nonemptiness:
            # the fall-through of `if not L: return ...` has L
            # nonempty, which is what licenses `L[-1]` -- exactly the
            # intersperse shape, where CPython would raise on the
            # empty list the guard already returned for.
            if loop.post_appends:
                gmin = dict(lc0.min_len or {})
                for gc, _gv in loop.guards:
                    if isinstance(gc, ast.UnaryOp) \
                            and isinstance(gc.op, ast.Not) \
                            and isinstance(gc.operand, ast.Name) \
                            and gc.operand.id in lc0.lists:
                        gmin[gc.operand.id] = max(
                            gmin.get(gc.operand.id, 0), 1)
                lc_app = _ListCtx(lc0.lists, lc0.safe_idx, lc0.take_idx,
                                  lc0.scaffold, gmin, lc0.pos_names,
                                  lc0.result_list, lc0.result_is_list,
                                  lc0.nonneg_names)
                pa_ts = [_int_expr(pe, names, fn.lineno, lc=lc_app)
                         for pe in loop.post_appends]
                ret_t = av + "".join(f" ++ [{t}]" for t in pa_ts)
            emit("", None)
            emit(f"def {_ident(spec_fn.name)} {binders} : {acc_ty} :=",
                 fn.lineno)
            if loop.start is None:
                fuel_call = f"({bound_t}).toNat 0"
            else:
                fuel_call = (f"(({bound_t}) - ({start_t})).toNat "
                             f"({start_t})")
            body_t = (f"let {av} := {_ident(gen_loop)} {argsp}"
                      f"{fuel_call} {init_t}; {ret_t}")
            emit("  " + _wrap_guards(loop.guards, body_t, names,
                                     fn.lineno, lc0, is_bool,
                                     is_list_ret), fn.lineno)
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

        # An `assert` is a proof OBLIGATION, exactly as Dafny reads it:
        # it must be proved, never assumed. Each becomes its own theorem
        # under the function's `requires`, so a false assert fails on
        # its own rather than silently strengthening the context.
        # A while function's only reachable asserts are POST-loop ones
        # (pre-loop and in-body are shape-rejected), and those belong
        # to the while path: their claims mention accumulators, which
        # this collector's parameter-only context cannot name.
        asserts = [] if wloop is not None \
            else _collect_asserts(list(fn.body))
        for ai, (st, claim, path) in enumerate(asserts):
            _no_old(st.test, st.lineno)
            _reject_undecidable_quantifier(claim, names, st.lineno, lc0)
            a_name = f"{spec_fn.name}_assert{ai}"
            _check_name(a_name, "generated assert obligation for",
                        st.lineno, taken)
            taken.add(a_name)
            a_hyps = []
            for hi, (hexpr, hline) in enumerate(
                    _parse_clause(spec_fn, "requires")):
                a_hyps.append(f"(ha{hi} : "
                              f"{_prop_expr(hexpr, names, hline, lc=lc0)})")
            # The branch conditions that reach this assert become
            # hypotheses: an assert under `if n > 0` owes its claim only
            # when that branch is taken.
            for pi_, (pcond, on_true) in enumerate(path):
                _reject_undecidable_quantifier(pcond, names, st.lineno,
                                               lc0)
                pt = _prop_expr(pcond, names, st.lineno, lc=lc0)
                a_hyps.append(f"(hp{pi_} : "
                              + (pt if on_true else f"(¬{pt})") + ")")
            a_sig = " ".join(x for x in [binders, *a_hyps] if x)
            emit("", None)
            emit(f"theorem {_ident(a_name)} {a_sig} :", st.lineno)
            emit(f"    {_prop_expr(claim, names, st.lineno, lc=lc0)} "
                 f":= by", st.lineno)
            for tl in ("  try unfold VeriPy.PyAbs",
                       "  try dsimp only",
                       "  try simp only [decide_eq_true_eq]",
                       "  repeat' split",
                       "  all_goals (try intros)",
                       "  all_goals (try simp_all)",
                       "  all_goals (first | omega | trivial)"):
                emit(tl, st.lineno)
            theorems.append(a_name)

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
        wf_extra: list[tuple[ast.expr, int]] = []
        earlier_posts: list[str] = []
        # Ensures are SPEC positions -- proof statements, never
        # executed -- so they translate under scaffold like invariants
        # do: computed indexing totalizes under the clause's own
        # bounds. Everything else lc0 carries rides along unchanged.
        post_lc = _ListCtx(lc0.lists, lc0.safe_idx, lc0.take_idx,
                           True, lc0.min_len, lc0.pos_names,
                           lc0.result_list, lc0.result_is_list,
                           lc0.nonneg_names)
        for expr, line in ensures:
            wf = _computed_read_wf(expr, post_lc, names)
            if wf is not None:
                wf_extra.append((wf, line))
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
        # The WF obligations join the GOAL as one synthetic post: the
        # spec theorem then certifies the contract AND every computed
        # read's in-boundedness, exactly as the Dafny backend's VCs
        # do. An out-of-range read makes the theorem unprovable
        # rather than quietly true about getD's default.
        for wfe, wfl in wf_extra:
            posts.append((_prop_expr(wfe, names, wfl, result=app,
                                     rename=rename,
                                     result_is_bool=is_bool,
                                     avoid=avoid, lc=post_lc), wfl))
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
        # A GUARDED loop must split before its facts are established:
        # `0 <= n` holds only in the branch the guard did not take, so
        # instantiating the loop lemma first fails on the other one.
        # Splitting first puts each branch in its own goal, and every
        # setup line is then attempted per-goal and skipped where it
        # does not apply.
        guarded = bool((loop.guards if loop is not None else [])
                       or (wloop.guards if wloop is not None else []))
        if guarded:
            emit("  try dsimp only", first_ensures_line)
            emit("  repeat' split", first_ensures_line)
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
            # Same per-branch treatment the for path gets: with a guard
            # the goal has already split, and these facts hold only in
            # the branch the guard did not take.
            wgp = "all_goals (try (" if guarded else ""
            wgs = "))" if guarded else ""
            wbr_h, wbr_n = _const_div_bridges(fn, spec_fn)
            wbr = "".join(h + "; " for h in wbr_h) + (
                f"all_goals (try simp only [{', '.join(wbr_n)}] at *); "
                if wbr_n else "")
            # The initial invariant instantiates at literal init
            # values, which surfaces closed prelude terms (`PyPow 2 0`)
            # and small literal residues (`PyMod 1 p`). Evaluate the
            # first with the prelude's own equations; for the second,
            # this is SPEC context, so the requires are in scope and
            # `(by omega)` can discharge the variable divisor's
            # positivity and the literal's range -- exactly what the
            # induction theorem could not do. Both guarded: a shape
            # without such residues skips them.
            emit(f"  {wgp}have hi0 : {_ident(gi)} {targsp}{w_inits} := by "
                 f"simp only [{_ident(gi)}]; {wbr}"
                 f"all_goals (try simp only [VeriPy.PyPow_zero]); "
                 f"all_goals (try (rw [VeriPy.PyMod_pos _ _ (by omega), "
                 f"Int.emod_eq_of_lt (by omega) (by omega)])); "
                 f"all_goals (try push_cast); "
                 f"all_goals (try omega); all_goals (try simp_all); "
                 f"all_goals (try intros); "
                 f"all_goals (first | omega | trivial){wgs}",
                 first_ensures_line)
            # The fuel is the measure at entry, so the fuel-bound
            # obligation is exactly "the measure starts non-negative".
            emit(f"  {wgp}have hfin := {_ident(gt)} {targsp}"
                 f"(({_ident(gm)} {targsp}{w_inits}).toNat + 1) {w_inits} "
                 f"hi0 (by simp only [{_ident(gm)}]; omega){wgs}",
                 first_ensures_line)
            emit(f"  {wgp}obtain ⟨hinv, hcond⟩ := hfin{wgs}",
                 first_ensures_line)
            # Post-loop asserts instantiate BEFORE the unfolding simp:
            # the obligation theorem wants hinv/hcond in FOLDED form,
            # and the accumulator arguments are left as `_` for Lean
            # to infer from hinv's own type (the projection terms are
            # long, and spelling them re-derives what unification
            # already knows).
            nreq = len(_parse_clause(spec_fn, "requires"))
            for pk in range(len(wloop.post_asserts)):
                pa = _ident(f"{spec_fn.name}_post_assert{pk}")
                pa_args = " ".join(
                    ["_" for _ in wloop.accs]
                    + [f"h{qi}" for qi in range(nreq)]
                    + ["hinv", "hcond"]
                    + [f"hpa{j}" for j in range(pk)])
                emit(f"  {wgp}have hpa{pk} := {pa} {targsp}{pa_args}{wgs}",
                     first_ensures_line)
            emit(f"  all_goals (try (simp only [{_ident(gi)}, "
                 f"{_ident(gc)}, decide_eq_false_iff_not] "
                 f"at hinv hcond))", first_ensures_line)
            # The bridges again, now that hinv carries the invariant in
            # unfolded form: that is where the floor divisions surface.
            for wb in wbr_h:
                emit(f"  {wb}", first_ensures_line)
            if wbr_n:
                emit(f"  all_goals (try simp only "
                     f"[{', '.join(wbr_n)}] at *)", first_ensures_line)
            # The proved exit equalities REWRITE the projection terms.
            # This is the payoff: `hpa : i_final = n + 1` turns the
            # nonlinear atom `(i_final - 1) * i_final` into
            # `(n + 1 - 1) * (n + 1)`, and add_sub_cancel then matches
            # it to the spec's own `n * (n + 1)` -- omega cannot
            # multiply, but it can use what a rewrite already did.
            for pk in range(len(wloop.post_asserts)):
                emit(f"  all_goals (try simp only [hpa{pk}] at *)",
                     first_ensures_line)
            if wloop.post_asserts:
                emit("  all_goals (try simp only [Int.add_sub_cancel] "
                     "at *)", first_ensures_line)
            # A QUANTIFIED invariant conjunct (the gcd divisor-set
            # class) needs structured handling: omega FAILS on the ∀
            # buried inside the conjunction it is handed (measured on
            # the real task -- fast failure, not divergence; an
            # earlier "omega diverges natively" reading of this was a
            # scratch-tooling artifact, a case-insensitive-filesystem
            # self-cat that fed lean a 58GB file), and the ladder
            # cannot instantiate a quantifier at the terms the
            # ensures actually needs. So: destructure the invariant so
            # every conjunct stands alone, then instantiate each ∀ at
            # the RESULT (ensures mention it) and at the goal's own
            # binder after intro (for ∀-shaped ensures). Every step
            # guarded: shapes without the conjunct skip it all.
            inv_conjs = (list(wloop.inv.values)
                         if isinstance(wloop.inv, ast.BoolOp)
                         and isinstance(wloop.inv.op, ast.And)
                         else [wloop.inv])

            def _is_quant(c: ast.expr) -> bool:
                return (isinstance(c, ast.Call)
                        and isinstance(c.func, ast.Name)
                        and c.func.id in ("all", "any"))

            q_idx = [ci for ci, c in enumerate(inv_conjs)
                     if _is_quant(c)]
            # The instantiation term must speak the language the goal
            # speaks. The top-level `unfold` turns the goal's function
            # applications into loop PROJECTIONS, so instantiating at
            # the folded application hands omega a second, unrelated
            # atom and the guarded side goal silently skips (measured:
            # every instantiation below no-opped). Bare-name returns
            # only; a computed return keeps honest incompleteness.
            ret_proj = None
            if isinstance(wloop.ret, ast.Name) \
                    and wloop.ret.id in wloop.accs:
                w_app = (f"({_ident(f'{spec_fn.name}_loop')} {targsp}"
                         f"(({_ident(gm)} {targsp}{w_inits}).toNat + 1) "
                         f"{w_inits})")
                ret_proj = w_app + _proj(
                    wloop.accs.index(wloop.ret.id), len(wloop.accs))
            if q_idx and len(inv_conjs) > 1 and ret_proj is not None:
                hj_names = [f"hj{ci}" for ci in range(len(inv_conjs))]
                emit(f"  {wgp}obtain ⟨{', '.join(hj_names)}⟩ := "
                     f"hinv{wgs}", first_ensures_line)
                # The exit condition rewrites the dead accumulator in
                # the OTHER hypotheses and the goal -- never `at *`,
                # which rewrites hcond itself to `0 = 0` and CLEARS
                # the one fact that refutes the dead disjunct
                # (measured: `1 ≤ x` from `x > 0 ∨ y > 0` became
                # unprovable because y = 0 was gone).
                emit(f"  all_goals (try simp only [hcond] at "
                     f"{' '.join(hj_names)} ⊢)", first_ensures_line)
                for ci in q_idx:
                    # At the result. The unfolding simp CURRIES the
                    # bound (`(A ∧ B) → C` becomes `A → B → C`), so
                    # the two-discharge form is tried first and the
                    # uncurried form kept as the fallback; each omega
                    # runs among STANDALONE, projection-language
                    # hypotheses.
                    emit(f"  all_goals (try (have hjr{ci} := hj{ci} "
                         f"{ret_proj} (by omega) (by omega)))",
                         first_ensures_line)
                    emit(f"  all_goals (try (have hjr{ci} := hj{ci} "
                         f"{ret_proj} (by omega)))", first_ensures_line)
                # Self and zero residues surface exactly here
                # (x % x, 0 % x).
                # true_and/iff_true finish what the residue lemmas
                # start: without them `(True ∧ True) ↔ RHS` just sits
                # there (measured), one True short of usable.
                emit("  all_goals (try simp only [VeriPy.PyMod_self, "
                     "VeriPy.PyMod_zero_left, true_and, and_true, "
                     "true_iff, iff_true] at *)",
                     first_ensures_line)
                # `repeat' split` splits if/match, NOT conjunctions --
                # every earlier task closed its posts-∧ whole via
                # omega, which a ∀-shaped conjunct forbids. Split it
                # so the quantified post stands alone for the intro.
                emit("  all_goals (try (repeat' apply And.intro))",
                     first_ensures_line)
                # ∀-shaped ensures: intro the binder, instantiate
                # there, and supply the below-the-divisor residue
                # (`x % d = x` for 0 ≤ x < d) that refutes the
                # too-big divisor.
                emit("  all_goals (try (intro d_ hd_))",
                     first_ensures_line)
                for ci in q_idx:
                    emit(f"  all_goals (try (have hjd{ci} := hj{ci} "
                         f"d_ (by omega) (by omega)))",
                         first_ensures_line)
                    emit(f"  all_goals (try (have hjd{ci} := hj{ci} "
                         f"d_ (by omega)))", first_ensures_line)
                emit(f"  all_goals (try (have hsm_ : VeriPy.PyMod "
                     f"{ret_proj} d_ = {ret_proj} := by "
                     f"rw [VeriPy.PyMod_pos _ _ (by omega)]; "
                     f"exact Int.emod_eq_of_lt (by omega) (by omega)))",
                     first_ensures_line)
        elif loop is not None and loop.search_test is not None:
            targs = " ".join(_ident(_tname(pn)) for pn in params)
            targsp = (targs + " ") if targs else ""
            t_bound = _int_expr(loop.bound, names, fn.lineno,
                                rename=rename, lc=lc0)
            t_init = _int_expr(loop.init, names, fn.lineno,
                               rename=rename, lc=lc0)
            gi_s = f"{spec_fn.name}_inv"
            gt_s = f"{spec_fn.name}_loop_inv"
            emit("  try dsimp only", first_ensures_line)
            # inv at entry: the user part under `false = false`, and
            # the flag-iff whose RHS is the EMPTY-PREFIX ∃ -- only
            # n = 0 is in range, and P(0) evaluates on the empty take.
            emit(f"  have hi0 : {_ident(gi_s)} {targsp}0 ({t_init}) "
                 f"false := by", first_ensures_line)
            emit(f"    simp only [{_ident(gi_s)}]", first_ensures_line)
            emit("    constructor", first_ensures_line)
            emit("    · intro _", first_ensures_line)
            emit("      all_goals (try push_cast)", first_ensures_line)
            emit("      all_goals (try simp_all [VeriPy.PySum])",
                 first_ensures_line)
            # A ∀-conjunct at entry ranges over [lo, lo+1)-style
            # windows whose only inhabitant is the start: name the
            # binder, pin it with omega, substitute, and the empty
            # take collapses (measured: anonymous intros left
            # `n✝ < 1 ⊢ 0 ≤ PySum (take n✝)` unreachable).
            emit("      all_goals (try (intro nz_ hz_))",
                 first_ensures_line)
            emit("      all_goals (try (obtain ⟨hz0_, hz1_⟩ := hz_))",
                 first_ensures_line)
            emit("      all_goals (try (intro hz1c_))",
                 first_ensures_line)
            emit("      all_goals (try (have hze_ : nz_ = 0 := by "
                 "omega))", first_ensures_line)
            emit("      all_goals (try (subst hze_))",
                 first_ensures_line)
            emit("      all_goals (try simp_all [VeriPy.PySum])",
                 first_ensures_line)
            emit("      all_goals (try intros)", first_ensures_line)
            emit("      all_goals (first | omega | trivial)",
                 first_ensures_line)
            emit("    · constructor", first_ensures_line)
            emit("      · intro hf_", first_ensures_line)
            emit("        exact absurd hf_ (by simp)",
                 first_ensures_line)
            emit("      · rintro ⟨n_, hn_, hp_⟩", first_ensures_line)
            emit("        have hz_ : n_ = 0 := by omega",
                 first_ensures_line)
            emit("        subst hz_", first_ensures_line)
            emit("        all_goals (try simp_all [VeriPy.PySum])",
                 first_ensures_line)
            emit("        all_goals (first | omega | trivial)",
                 first_ensures_line)
            emit(f"  have hfin := {_ident(gt_s)} {targsp}"
                 f"({t_bound}).toNat 0 ({t_init}) false hi0 "
                 f"(by omega) (by omega)", first_ensures_line)
            emit(f"  obtain ⟨hfu_, hfiff_⟩ := hfin",
                 first_ensures_line)
            emit(f"  all_goals (try rw [Int.toNat_of_nonneg "
                 f"(by omega : (0:Int) ≤ {t_bound})] at hfiff_)",
                 first_ensures_line)
            emit("  all_goals (try simp only [Int.toNat_natCast, "
                 "Int.zero_add] at hfiff_)", first_ensures_line)
            emit("  all_goals (try (exact hfiff_))",
                 first_ensures_line)
            emit("  all_goals (try simp_all)", first_ensures_line)
            emit("  all_goals (try intros)", first_ensures_line)
            emit("  all_goals (first | omega | trivial)",
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
            t_start = ("0" if loop.start is None
                       else _int_expr(loop.start, names, fn.lineno,
                                      rename=rename, lc=lc0))
            emit("  try dsimp only", first_ensures_line)
            # With a guard the goal has already split, and the loop's
            # facts hold only in the branch the guard did not take, so
            # each is attempted per-goal and skipped where it does not
            # apply.
            gp = "all_goals (try (" if guarded else ""
            gs = "))" if guarded else ""
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
                           f"{targsp}({t_start}) {t_init} := by",
                           f"    simp only "
                           f"[{_ident(f'{spec_fn.name}_inv')}]",
                           "    constructor",
                           *("  " + x for x in b)):
                    emit(tl, first_ensures_line)
            else:
                # And.intro splits the goal-side conjunction FIRST:
                # omega cannot split a goal ∧ that carries ∀-conjuncts
                # (the gcd lesson, goal-side -- measured on the
                # intersperse hi0, whose three-conjunct invariant with
                # vacuous ∀s failed the unsplit ladder).
                emit(f"  {gp}have hi0 : {_ident(f'{spec_fn.name}_inv')} "
                     f"{targsp}({t_start}) {t_init} := by "
                     f"simp only [{_ident(f'{spec_fn.name}_inv')}]; "
                     f"all_goals (try (repeat' apply And.intro)); "
                     f"all_goals (try push_cast); all_goals (try omega); "
                     f"all_goals (try simp_all [VeriPy.PySum]); "
                     f"all_goals (try intros); "
                     f"all_goals (first | omega | trivial){gs}",
                     first_ensures_line)
            if loop.start is None:
                hfin_fuel, hfin_i = f"({t_bound}).toNat", "0"
            else:
                hfin_fuel = f"(({t_bound}) - ({t_start})).toNat"
                hfin_i = f"({t_start})"
            # Both side obligations go through omega, which reasons
            # about toNat and max natively: `0 ≤ start` needs the
            # requires in context (present here), and
            # `start + (bound - start).toNat ≤ max bound start` is TRUE
            # even for the empty range, which the plain-bound form was
            # not.
            emit(f"  {gp}have hfin := {_ident(f'{spec_fn.name}_loop_inv')} "
                 f"{targsp}{hfin_fuel} {hfin_i} {t_init} hi0 (by omega) "
                 f"(by omega){gs}",
                 first_ensures_line)
            emit(f"  all_goals (try (simp only "
                 f"[{_ident(f'{spec_fn.name}_inv')}] at hfin))",
                 first_ensures_line)
            # Guarded like every other generated step: an invariant
            # that never mentions the loop index leaves no `↑bound.toNat`
            # in hfin once the invariant is unfolded, and an unguarded
            # `rw` then fails the whole proof (measured: a true spec
            # whose invariant was index-free failed as postcondition).
            if loop.start is None:
                emit(f"  all_goals (try rw [Int.toNat_of_nonneg "
                     f"(by omega : (0:Int) ≤ {t_bound})] at hfin)",
                     first_ensures_line)
            else:
                # Two guarded steps: cast the fuel back to
                # `bound - start` (provable only for the non-empty
                # range, hence try), then collapse the index sum so
                # hfin's atoms mention the bound itself.
                emit(f"  all_goals (try rw [Int.toNat_of_nonneg "
                     f"(by omega : (0:Int) ≤ (({t_bound}) - "
                     f"({t_start})))] at hfin)", first_ensures_line)
                emit(f"  all_goals (try rw [show (({t_start}) + "
                     f"(({t_bound}) - ({t_start}))) = ({t_bound}) "
                     f"from by omega] at hfin)", first_ensures_line)
            # For a `range(len(xs))` loop the invariant lands at
            # `take (0 + ↑xs.length).toNat`: normalize the casts and
            # collapse `take xs.length` to the whole list so hfin's
            # atoms match the ensures translation (`PySum xs`). Inert
            # (hence `try`) when no list is involved.
            emit("  all_goals (try simp only [Int.toNat_natCast, "
                 "Int.zero_add, List.take_length] at hfin)",
                 first_ensures_line)
            # The prefix-range search endgame (is_prime class): an
            # early-return loop over range(start, bound) whose spec
            # quantifies a WIDER range. hfin's iff covers the loop's
            # own window, so each ensures implication is proved by
            # reading the loop result off its antecedent: the ∀-post
            # extends past the window index by the `#@ proof` gap
            # facts, and the ∃-post transports the witness the failed
            # search produced. One atomic `try`: any shape mismatch
            # rolls the whole script back to the generic path. Coded
            # against the measured pre-simp goal of exactly this
            # posts pattern (bool-implication, ∀-spec, ∃-spec).
            if loop.acc_bool and loop.start is not None:
                b_str = (f"(({t_start}) + ((((({t_bound}) - "
                         f"({t_start}))).toNat : Int)))")
                gap_haves = []
                for gi_, gclause in enumerate(spec_fn.by_kind("proof")):
                    gtext = (gclause.desugared
                             if gclause.desugared is not None
                             else gclause.raw)
                    try:
                        gcall = ast.parse(gtext, mode="eval").body
                        gargs = " ".join(
                            "(" + _int_expr(a, names, gclause.line,
                                            rename=rename, lc=lc0) + ")"
                            for a in gcall.args)
                    except (SyntaxError, EncodeError):
                        continue
                    gap_haves.append(
                        f"first | (have hgap{gi_} := "
                        f"{gcall.func.id} {gargs} (by omega)) | "
                        f"(have hgap{gi_} := {gcall.func.id} {gargs})")
                app_b = (f"{_ident(f'{spec_fn.name}_loop')} "
                         f"{targsp}{hfin_fuel} {hfin_i} {t_init}")
                # The frontend desugars `A ==> B` to `(not A) or B`,
                # so every post is an ∨-goal in BOTH guard branches --
                # never an implication (measured: intro failed with
                # "no additional binders"). Each conjunct therefore
                # case-splits on the loop result with Classical.em.
                script = [
                    "  all_goals (try (",
                    "    refine ⟨?_, ?_, ?_⟩",
                    "    · first",
                    "        | (right",
                    "           omega)",
                    "        | (left",
                    "           simp)",
                    f"    · rcases Classical.em ({app_b} = true) "
                    "with hres_ | hres_",
                    "      · right",
                    "        have hall_ := hfin.mp hres_",
                    "        intro k_ hk_",
                    f"        by_cases hlt_ : k_ < {b_str}",
                    "        · first | (exact hall_ k_ ⟨hk_.1, hlt_⟩) "
                    "| (exact hall_ k_ hk_.1 hlt_)",
                ]
                lead = "        · "
                for gh in (gap_haves or ["skip"]):
                    script.append(lead + gh)
                    lead = "          "
                script += [
                    f"          have hke_ : k_ = ({t_bound}) "
                    ":= by omega",
                    "          rw [hke_]",
                    "          omega",
                    "      · left",
                    "        exact hres_",
                    f"    · rcases Classical.em ({app_b} = true) "
                    "with hres_ | hres_",
                    "      · left",
                    "        intro hc_",
                    "        exact hc_.1 hres_",
                    "      · right",
                    "        have hnotall_ := fun hall_ => "
                    "hres_ (hfin.mpr hall_)",
                    "        obtain ⟨j_, hj_⟩ := "
                    "Classical.not_forall.mp hnotall_",
                    "        first",
                    "          | (obtain ⟨hjb_, hjp_⟩ := "
                    "Classical.not_imp.mp hj_",
                    "             exact ⟨j_, ⟨hjb_.1, by omega⟩, "
                    "Decidable.not_not.mp hjp_⟩)",
                    "          | (obtain ⟨hj2_, hjr_⟩ := "
                    "Classical.not_imp.mp hj_",
                    "             obtain ⟨hjB_, hjp_⟩ := "
                    "Classical.not_imp.mp hjr_",
                    "             exact ⟨j_, ⟨hj2_, by omega⟩, "
                    "Decidable.not_not.mp hjp_⟩)))",
                ]
                for tl in script:
                    emit(tl, first_ensures_line)
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
                        # The helper's statement names the FUNCTION,
                        # but the loop facts (hinv, hcond) talk about
                        # the loop application -- so the sub-proof must
                        # unfold the function exactly as the main
                        # endgame does, or simp_all has a folded
                        # application on one side and projections on
                        # the other and closes neither (measured on
                        # gcd: `1 <= greatest_common_divisor a b` with
                        # x > 0 sitting unusable in hinv).
                        for tl in (f"    try unfold "
                                   f"{_ident(spec_fn.name)}",
                                   "    try unfold VeriPy.PyAbs",
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
        # The NESTED-SEARCH spec endgame: hfin carries the
        # ¬-wrapped ∀-chain, the ensures wants the ∃-chain -- the
        # classical duality, term-mode at the invariant's depth, with
        # both bound spellings (simp curries them nondeterministically)
        # as alternatives.
        if loop is not None and loop.search_test is None \
                and getattr(loop, "neg_wrap_depth", 0) >= 2:
            D = loop.neg_wrap_depth
            lam_c = " ".join(f"a{k}_ ha{k}_" for k in range(1, D + 1))
            lam_u = " ".join(f"a{k}_ h{k}a_ h{k}b_"
                             for k in range(1, D + 1))
            wit_c = "heq_"
            for k in range(D, 0, -1):
                wit_c = f"⟨a{k}_, ha{k}_, {wit_c}⟩"
            wit_u = "heq_"
            for k in range(D, 0, -1):
                wit_u = f"⟨a{k}_, ⟨h{k}a_, h{k}b_⟩, {wit_u}⟩"
            pat = "hp_"
            for k in range(D, 0, -1):
                pat = f"⟨a{k}_, ha{k}_, {pat}⟩"
            app_c = " ".join(f"a{k}_ ha{k}_" for k in range(1, D + 1))
            app_u = " ".join(f"a{k}_ ha{k}_.1 ha{k}_.2"
                             for k in range(1, D + 1))
            for tl in (
                "  all_goals (try (first",
                "    | (constructor",
                "       · intro hfx_",
                "         refine Classical.byContradiction "
                "(fun hne_ => ?_)",
                f"         exact (hfin.mpr (fun {lam_c} heq_ => "
                f"hne_ {wit_c})) hfx_",
                f"       · rintro {pat}",
                "         refine Classical.byContradiction "
                "(fun hnf_ => ?_)",
                f"         exact (hfin.mp hnf_) {app_c} hp_)",
                "    | (constructor",
                "       · intro hfx_",
                "         refine Classical.byContradiction "
                "(fun hne_ => ?_)",
                f"         exact (hfin.mpr (fun {lam_u} heq_ => "
                f"hne_ {wit_u})) hfx_",
                f"       · rintro {pat}",
                "         refine Classical.byContradiction "
                "(fun hnf_ => ?_)",
                f"         exact (hfin.mp hnf_) {app_u} hp_)))",
            ):
                emit(tl, first_ensures_line)
        # The PARITY-APPEND spec endgame (intersperse): the ensures
        # read through the trailing append, so each ∀-post gets the
        # seam script -- old indices through GetD_append_left into
        # hfin's invariant, the seam through GetD_append_last with the
        # constant-div bridges collapsing the parity residue. Gated
        # tightly and atomic: any mismatch rolls back to the ladder.
        if loop is not None and getattr(loop, "post_appends", None) \
                and (loop.acc_list
                     and any(isinstance(nd, ast.BinOp)
                             and isinstance(nd.op, ast.Mod)
                             for nd in ast.walk(loop.inv))):
            napp_s = len(loop.post_appends)
            n_conj_s = (len(loop.inv.values)
                        if isinstance(loop.inv, ast.BoolOp)
                        and isinstance(loop.inv.op, ast.And) else 1)
            n_posts = len(posts)
            sj = ", ".join(f"hf{ci}_" for ci in range(n_conj_s))
            sph = ", ".join("?_" for _ in range(n_posts))
            app_s = (f"({_ident(f'{spec_fn.name}_loop')} {targsp}"
                     + (f"(({t_bound}) - ({t_start})).toNat "
                        f"({t_start})" if loop.start is not None
                        else f"({t_bound}).toNat 0")
                     + " ([] : List Int))")
            sinst = " | ".join(
                [f"(exact hf{ci}_ k_ ⟨hk_.1, by omega⟩)"
                 for ci in range(n_conj_s)]
                + [f"(exact hf{ci}_ k_ hk_.1 (by omega))"
                   for ci in range(n_conj_s)]
                + ["trivial"])
            sbr_h, sbr_n = _const_div_bridges(fn, spec_fn)
            left_chain_s = ", ".join(
                ["VeriPy.GetD_append_left _ _ _ (by "
                 "simp [List.length_append]; try omega)"]
                * (napp_s - 1)
                + ["VeriPy.GetD_append_left _ _ _ hin_"])
            for tl in (
                "  all_goals (try (",
                f"    generalize hfold_ : {app_s} = fold_",
                "    (try rw [hfold_] at hfin)",
                f"    obtain ⟨{sj}⟩ := hfin",
                *(f"    {h_}" for h_ in sbr_h),
                f"    refine ⟨{sph}⟩ <;>",
                "    first",
                "      | (simp [List.length_append]; all_goals omega)",
                "      | (intro k_ hk_",
                "         all_goals (try simp_all)",
                "         all_goals omega)",
                "      | (intro k_ hk_",
                "         simp only [List.length_append, "
                "List.length_cons, List.length_nil] at hk_",
                "         rcases Classical.em ((k_).toNat "
                "< fold_.length) with hin_ | hout_",
                f"         · rw [{left_chain_s}]",
                f"           first | {sinst}",
            ):
                emit(tl, first_ensures_line)
            for j in range(napp_s):
                outer_s = ", ".join(
                    ["VeriPy.GetD_append_left _ _ _ (by "
                     "simp [List.length_append]; try omega)"]
                    * (napp_s - 1 - j))
                lead = ("         · " if j == 0 else "           · ")
                if j < napp_s - 1:
                    emit(f"{lead}rcases Classical.em ((k_).toNat = "
                         f"fold_.length + {j}) with hs{j}_ | "
                         f"hsn{j}_", first_ensures_line)
                    lead = "           · "
                seam_pos = (f"fold_.length + {j}" if j
                            else "fold_.length")
                ind = "           "
                emit(f"{lead}"
                     + (f"rw [{outer_s}]; " if outer_s else "")
                     + f"rw [show (k_).toNat = {seam_pos} by omega]",
                     first_ensures_line)
                if j > 0:
                    pref = " ++ ".join(
                        "[" + _int_expr(pe, names, fn.lineno,
                                        rename=rename, lc=post_lc)
                        + "]"
                        for pe in loop.post_appends[:j])
                    emit(f"{ind}rw [show (fold_.length + {j}) = "
                         f"(fold_ ++ {pref}).length by "
                         f"simp [List.length_append]; try omega]",
                         first_ensures_line)
                emit(f"{ind}rw [VeriPy.GetD_append_last]",
                     first_ensures_line)
                if sbr_n:
                    emit(f"{ind}(try simp only "
                         f"[{', '.join(sbr_n)}] at *)",
                         first_ensures_line)
                emit(f"{ind}(try (have hdiv_ : k_ / 2 = "
                     f"(({t_bound})) := by omega)); "
                     f"(try rw [hdiv_])", first_ensures_line)
                emit(f"{ind}all_goals (first | rfl | trivial | omega "
                     f"| (left; omega) | (right; first | rfl | "
                     f"trivial | omega))", first_ensures_line)
            emit("      )", first_ensures_line)
            emit("  ))", first_ensures_line)
        if is_list_ret:
            emit("  all_goals (try simp only "
                 "[List.getD_eq_getElem?_getD, List.getElem?_map, "
                 "List.length_map])", first_ensures_line)
        if _FILTER_PREDS and loop is None and wloop is None:
            # The filtered-comprehension class: split the goal into
            # one hole per post, then three guarded finishers.
            # Definitional posts (`result == [x for x in l if P]`)
            # close by rfl. Count-preservation posts intro the
            # membership AND the recovered antecedent, then rewrite
            # with Count_filter_of_pos at the EXPLICIT predicate --
            # rw's higher-order unification would otherwise guess a
            # constant function and miss the pattern. Membership
            # posts destructure mem_filter. Untouched goals flow to
            # the generic finishers below.
            if len(posts) > 1:
                holes = ", ".join("?_" for _ in posts)
                emit(f"  refine ⟨{holes}⟩", first_ensures_line)
            emit("  all_goals (try rfl)", first_ensures_line)
            for fpred in _FILTER_PREDS:
                emit(f"  all_goals (try (intro x_ hx_ hp_; "
                     f"rw [VeriPy.Count_filter_of_pos {fpred} _ _ "
                     f"(decide_eq_true hp_)]))", first_ensures_line)
            emit("  all_goals (try (intro x_ hx_; "
                 "simp only [List.mem_filter, decide_eq_true_eq] "
                 "at hx_; "
                 "first | exact hx_.1 | exact hx_.2 | omega))",
                 first_ensures_line)
        if _SORTED_UNIQUE_USED and loop is None and wloop is None:
            # The sorted-unique class: one hole per post, then the
            # pack's three spec-shaped lemmas as guarded finishers
            # (strict adjacency, result-elements-in-source,
            # source-elements-in-result). Bound side conditions fall
            # to omega under the intro'd binder hypothesis; WF
            # conjuncts and anything else flow to the generic
            # finishers below.
            if len(posts) > 1:
                holes = ", ".join("?_" for _ in posts)
                emit(f"  refine ⟨{holes}⟩", first_ensures_line)
            emit("  all_goals (try (intro i_ hb_; first "
                 "| exact VeriPy.SortedUnique_adjacent _ _ "
                 "(by omega) (by omega) "
                 "| exact VeriPy.SortedUnique_getD_mem_src _ _ "
                 "(by omega) (by omega) "
                 "| exact VeriPy.GetD_mem_SortedUnique _ _ "
                 "(by omega) (by omega)))", first_ensures_line)
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
        # A WF conjunct carrying TWO totalized reads is a conjunction
        # of bounded ∀s, which `intros` cannot enter: split it and
        # peel each side, guarded so any goal the shape does not fit
        # is left for the finisher line (constructor's failure — or
        # omega's on a non-linear side — backtracks the whole try).
        emit("  all_goals (try (constructor <;> (intros; omega)))",
             first_ensures_line)
        if wloop is not None:
            # The SQUARE-MAXIMALITY move (the isqrt class, cataloged
            # by the triple run): "no k in range beats the answer"
            # splits on k ≤ result; the beaten side closes by
            # squaring monotonicity against the exit condition — Z3
            # applies that natively, the fixed ladder needs SqLeSq
            # spelled. The posts-∧ splits first so the ∀-post stands
            # alone; both ∨ orientations offered; any goal the shape
            # does not fit fails the alternatives and the try
            # rescues untouched.
            ret_w = (f"({_ident(f'{spec_fn.name}_loop')} {targsp}"
                     f"(({_ident(gm)} {targsp}{w_inits}).toNat + 1) "
                     f"{w_inits})")
            emit("  all_goals (try (repeat' apply And.intro))",
                 first_ensures_line)
            emit("  all_goals (try (intro d_ hd_))",
                 first_ensures_line)
            emit("  all_goals (try (intro hd2_))", first_ensures_line)
            emit(f"  all_goals (try (rcases Classical.em "
                 f"(d_ ≤ {ret_w}) with hqle_ | hqgt_ <;> first "
                 f"| exact Or.inr hqle_ "
                 f"| exact Or.inl hqle_ "
                 f"| (left; have hsq_ := VeriPy.SqLeSq ({ret_w} + 1) "
                 f"d_ (by omega) (by omega); omega) "
                 f"| (right; have hsq_ := VeriPy.SqLeSq ({ret_w} + 1) "
                 f"d_ (by omega) (by omega); omega) "
                 f"| omega))", first_ensures_line)
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
