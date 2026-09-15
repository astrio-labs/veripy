# Specification language

This guide describes the maintained `#@` interface. Annotation parsing is shared,
but admission and proof support depend on the selected backend. See
[supported fragments](SUPPORTED-FRAGMENTS.md) and [Lean](LEAN.md).

Specs are comments beginning `#@`. CPython ignores them; the spec parser does not.

## Clauses

| Clause | Placement | Interpretation |
| --- | --- | --- |
| `#@ verified` | contract block above `def` | marks the function as opted in |
| `#@ requires EXPR` | contract block above `def` | proof precondition; entry check when runtime contracts or guards are used |
| `#@ ensures EXPR` | contract block above `def` | proof postcondition; runtime check when executable contracts or postcondition guards are enabled |
| `#@ ghost_ensures EXPR` | contract block above `def` | not runtime evaluated; a real Dafny postcondition, checked at every return and available at helper calls |
| `#@ invariant EXPR` | first lines inside a loop body | **parsed and recorded, not enforced at runtime** — used by supported Dafny and Lean loop encodings |
| `#@ decreases EXPR` | contract block or loop body | a proof termination measure; not enforced by ordinary runtime contracts |
| `#@ proof LemmaName(args…)` | function body, before the statement it precedes | backend-specific proof hook with checked sidecar support; ignored by CPython |

The **contract block** is the contiguous run of `#@` lines ending on the line directly above the `def` (no blank lines inside the block). `mutates` and `extern` are reserved words, not yet in the grammar.

## Expression language

`EXPR` is a Python expression (parsed with `ast.parse`) extended with implication, biconditional and quantified forms, removed by desugaring before parsing:

| Construct | Meaning | Desugars to |
| --- | --- | --- |
| `A <==> B` | biconditional (loosest precedence, below `==>`) | `bool(A) == bool(B)` |
| `A ==> B` | implication (right-associative) | `(not (A)) or (B)` |
| `forall x in D[, y in E …] :: BODY` | universal over finite iterable domain(s) | `all((BODY) for x in (D) …)` |
| `exists x in D[, y in E …] :: BODY` | existential over finite iterable domain(s) | `any((BODY) for x in (D) …)` |
| `result` | the function's return value | *(ensures and ghost_ensures only)* |
| `old(p)` | value of parameter `p` at function entry (runtime ensures use a deep copy) | *(ensures, ghost_ensures, invariants and proof arguments; `p` must be a bare parameter name)* |
| `ghost("Predicate", args…)` | call to a defined, verified sidecar predicate | *(invariants, proof arguments and ghost_ensures only; Dafny)* |
| `raised()` / `raised("ClassName")` | modeled exception occurrence or hierarchy membership | *(supported outcome contracts; see below)* |

A quantifier's body extends to the end of the expression (Dafny convention); parenthesize to limit it. Implications written inside a call's argument list must be parenthesized. Prefer `<==>` over hand-written `(A) == (B)` for iffs: the explicit form silently becomes a chained comparison if the parentheses are dropped — the trap that motivated adding `<==>` in v0.1.

Plain Python's `all(... for ...)` / `any(... for ...)` are equally valid and equivalent; `forall`/`exists` are readability sugar. Names available in specs: the function's parameters, quantifier-bound variables, module-level names, and a safe builtin allowlist (`len`, `range`, `sum`, `min`, `max`, `abs`, `sorted`, `all`, `any`, …).

## Interpretation and naming

Quantifier domains are explicit and finite. `==>` desugars to Python `not/or`
with short-circuit behavior. Ordinary runtime contracts must be executable, but
static ghost predicates are proof-only. General `old(expr)` is unsupported;
`old(p)` takes a bare parameter name and denotes its entry value.

`ghost_ensures` is a checked Dafny postcondition on every return. Its predicate
definitions and any supporting lemmas must verify. It is not an unchecked
assumption, a runtime condition, or a Lean annotation. The public Lean encoder
rejects it even though Lean has its own checked proof-support interface.

Dafny `proof` clauses are single lemma calls whose declarations must pass the
sidecar gate. Lean uses its admitted proof hooks and `.proofs.lean` declarations;
Dafny lemmas are not portable to Lean. See [the Lean guide](LEAN.md).

In postconditions, `result` denotes the returned value. A Dafny local named
`result` is preserved as a distinct generated local. In invariants, decreases
clauses and proof arguments it denotes the local when one is bound. A parameter
named `result` is rejected except for the explicit buffer-name mechanism below.
Other reserved specification names and collisions are checked by the frontend
and backend. `mutates` and `extern` are not implemented annotation clauses.

Runtime emission, guards and formal backends do not accept identical expression
sets. Parsing a clause does not establish that a backend can verify it or that
a guard can execute it. Unsupported uses must be reported as admission errors.

## Grammar sketch

```
spec_comment ::= "#@" clause
clause       ::= "verified"
               | ("requires" | "ensures" | "ghost_ensures" | "invariant" | "decreases") expr
               | "proof" NAME "(" [py_expr ("," py_expr)*] ")"
expr         ::= quant | iff
quant        ::= ("forall" | "exists") binder ("," binder)* "::" expr
binder       ::= NAME "in" py_expr
iff          ::= impl ("<==>" expr)?            # loosest
impl         ::= py_expr ("==>" expr)?          # right-associative
py_expr      ::= <Python expression grammar>, names as restricted above
```

## Explicit buffer and exception observations

The `dafny-outcomes` backend accepts `raised()` and, for a modeled exception
hierarchy, `raised("InvalidFormat")` (or another declared class name). The latter
includes subclasses. Lean supports the selected exception contracts used by the
validation cohort in ordinary `ensures`, with its own checked error model.
Ordinary Dafny guards reject outcome-specific clauses. Use the outcome guard
backend for supported exception-aware runtime checks; ghost contracts remain static.

The `dafny-buffers` backend adds these specification-only forms:

```python
#@ requires allow_buffer_alias("result", "scanline")
#@ requires len(buffer("result")) == len(scanline)
#@ ensures forall i in range(len(buffer("result"))) :: 0 <= buffer("result")[i] < 256
```

`disjoint_buffers()` is the alternative policy requiring every buffer argument
to be distinct. An allowed pair may alias or be distinct; all other argument
pairs must remain distinct. `buffer("name")` observes the current buffer and
`old_buffer("name")` its entry snapshot. A buffer parameter named `result` is
permitted in this backend, but an ambiguous bare return-result observation is
not. These forms do not execute inside upstream function bodies.
