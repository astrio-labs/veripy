# `#@` Spec Grammar — v0.2

> **Status: v0.2** — v0.1 (frozen after the grammar-contact exercise) plus the `#@ proof` clause — 20 real HumanEval/MBPP tasks annotated, verified, and mutation-tested with one additive change (`<==>`); findings and deferred extensions in [GRAMMAR-CONTACT.md](GRAMMAR-CONTACT.md). Every change lands here first.

Specs are comments beginning `#@`. CPython ignores them; the spec parser does not.

## Clauses

| Clause | Placement | M0 runtime semantics |
| --- | --- | --- |
| `#@ verified` | contract block above `def` | marks the function as opted in |
| `#@ requires EXPR` | contract block above `def` | checked at entry (icontract `require`) |
| `#@ ensures EXPR` | contract block above `def` | checked at exit (icontract `ensure`) |
| `#@ invariant EXPR` | first lines inside a loop body | **parsed and recorded, not enforced at runtime** — consumed by the Dafny backend (M1) |
| `#@ decreases EXPR` | contract block or loop body | parsed and recorded, not enforced — Dafny backend (M1) |
| `#@ proof LemmaName(args…)` | function body, before the statement it precedes | ghost lemma invocation for the proof backend (lemmas live in the `<stem>.proofs.dfy` sidecar); ignored at runtime |

The **contract block** is the contiguous run of `#@` lines ending on the line directly above the `def` (no blank lines inside the block). `mutates` and `extern` are reserved words, not yet in the grammar.

## Expression language

`EXPR` is a Python expression (parsed with `ast.parse`) extended with three constructs, removed by desugaring before parsing:

| Construct | Meaning | Desugars to |
| --- | --- | --- |
| `A <==> B` | biconditional (loosest precedence, below `==>`) | `bool(A) == bool(B)` |
| `A ==> B` | implication (right-associative) | `(not (A)) or (B)` |
| `forall x in D[, y in E …] :: BODY` | universal over finite iterable domain(s) | `all((BODY) for x in (D) …)` |
| `exists x in D[, y in E …] :: BODY` | existential over finite iterable domain(s) | `any((BODY) for x in (D) …)` |
| `result` | the function's return value | *(ensures only)* |
| `old(p)` | value of parameter `p` at function entry (deep copy) | *(ensures only; `p` must be a bare parameter name in v0)* |

A quantifier's body extends to the end of the expression (Dafny convention); parenthesize to limit it. Implications written inside a call's argument list must be parenthesized. Prefer `<==>` over hand-written `(A) == (B)` for iffs: the explicit form silently becomes a chained comparison if the parentheses are dropped — the trap that motivated adding `<==>` in v0.1.

Plain Python's `all(... for ...)` / `any(... for ...)` are equally valid and equivalent; `forall`/`exists` are readability sugar. Names available in specs: the function's parameters, quantifier-bound variables, module-level names, and a safe builtin allowlist (`len`, `range`, `sum`, `min`, `max`, `abs`, `sorted`, `all`, `any`, …).

## Decisions (v0)

1. **Quantifier domains are explicit and finite** (`forall i in range(len(xs)) :: …`), not guard-style unbounded (`forall i :: 0 <= i < len(xs) ==> …`). Rationale: M0 is runtime-first — every spec must be *executable* so CrossHair/icontract can evaluate it, and the bounded form lowers to Dafny logic later via the comprehension→logic rule in the catalog ([ARCHITECTURE.md §7](ARCHITECTURE.md)). Guard-style unbounded quantifiers are a candidate addition for the proof backend (they cannot be runtime-checked; they would join the "assumed, not checked" set at boundaries).
2. **`==>` desugars to `not/or`**, preserving Python's short-circuit semantics — the guard idiom `i < len(xs) ==> xs[i] > 0` is well-defined exactly like the catalog's truthiness rule requires.
3. **`old()` is restricted to bare parameter names** in v0 so the entry snapshot is a simple deep copy per parameter. General `old(expr)` is a known extension.
4. **`#@ proof` is ghost-only by construction** (v0.2): it must be a single lemma call, the sidecar may contain only lemma/function/predicate declarations, and Dafny type-checks ghostness — proof additions cannot affect program state. Arguments are ordinary spec expressions.
5. **Reserved words:** `forall`, `exists`, `result`, `old` (plus `mutates`, `extern` for later). Code using these as identifiers is outside the fragment.

## Grammar sketch

```
spec_comment ::= "#@" clause
clause       ::= "verified"
               | ("requires" | "ensures" | "invariant" | "decreases") expr
               | "proof" NAME "(" [py_expr ("," py_expr)*] ")"
expr         ::= quant | iff
quant        ::= ("forall" | "exists") binder ("," binder)* "::" expr
binder       ::= NAME "in" py_expr
iff          ::= impl ("<==>" expr)?            # loosest
impl         ::= py_expr ("==>" expr)?          # right-associative
py_expr      ::= <Python expression grammar>, names as restricted above
```
