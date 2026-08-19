# Fragment Semantics — big-step rules and the simulation statement

> **Status: v1 fragment, preamble 0.7.** This is the paper-style companion to
> the lowering catalog ([ARCHITECTURE.md §7](ARCHITECTURE.md)): a big-step
> operational semantics for the verified fragment and the statement of the
> simulation claim the encoder is built to preserve. It is **not mechanized**;
> the translation-validation harness (§6, `veripy difftest`) is the standing
> empirical check of exactly this claim, and the per-construct table at the end
> records which rules it exercises.

## 1. Values and state

The fragment computes over five value sorts:

| sort | notation | CPython carrier | Dafny model |
| --- | --- | --- | --- |
| integers | `n ∈ ℤ` | `int` (arbitrary precision) | `int` |
| booleans | `b ∈ 𝔹` | `bool` | `bool` |
| strings | `s ∈ Σ*` | `str` (immutable) | `string` (`seq<char>`) |
| lists | `[v₁, …, vₖ]` | `list` (mutable) | `seq<T>` (value) |
| optionals | `None ∣ some v` | `None` / the value | `PyOpt<T>` |

`bool` is **not** a subsort of `int` in the fragment, although it is in
CPython — the conformance checker types every expression precisely, and the
boundary guards enforce exactness (`type(x) is int`) at entry, so no fragment
execution ever observes a `True` flowing into an `int` position.

A **state** `σ` maps local names to values. Parameters are immutable
(ownership + copy-in); list-typed locals additionally carry the *ownership
facts* the encoder tracks (fresh/unaliased/frozen), which are static
artifacts — they do not appear in σ, but the admission rules below are only
stated for programs the conformance checker accepts, so every `append`
target is known unaliased and every iterated list is known frozen.

## 2. Judgments

Expressions may diverge only through partiality, never loops (they contain
none), so their judgment is total up to the modeled errors:

    σ ⊢ e ⇓ v                     (evaluates to value)
    σ ⊢ e ⇓ err(E)                (raises E ∈ {IndexError, ValueError, TypeError, ZeroDivisionError})

Statements produce an outcome:

    σ ⊢ st ⇓ σ′                   (falls through)
    σ ⊢ st ⇓ return v             (function returns)
    σ ⊢ st ⇓ err(E)               (E as above, plus AssertionError)

`err` outcomes propagate through every rule (elided below). The Dafny model
has no exceptions: each `err` case corresponds to a **proof obligation**
(the `requires` of a preamble function, an `assert`, or a well-formedness
VC), so *a verified function is one whose executions from guard-passing
inputs never take an `err` transition* — that is the content of clause (a)
of the simulation statement.

## 3. Expression rules (selected)

The complete rule-per-construct listing coincides with the lowering catalog;
the rules here are the ones where CPython's semantics diverge from the naïve
mathematical reading, because these are where an encoder bug would hide.

**Floor division and modulo** (divisor `d ≠ 0`, else `err(ZeroDivisionError)`):

    n // d  =  ⌊n / d⌋                       n % d  =  n − d·⌊n / d⌋

so the result of `%` has the sign of the divisor. Dafny's `/` and `%` are
Euclidean; the preamble's `PyFloorDiv`/`PyMod` are definitionally equal to
the equations above (differentially tested across sign combinations).

**Indexing** (`xs` of length k):

    σ ⊢ xs[i] ⇓ xs[i]        if 0 ≤ i < k
    σ ⊢ xs[i] ⇓ xs[k + i]    if −k ≤ i < 0
    σ ⊢ xs[i] ⇓ err(IndexError)   otherwise

`PyIndex(i, k)` carries `requires −k ≤ i < k` — exactly the error condition —
and the encoder emits the bare index only when nonnegativity is provable
from the static context (literals and 0-based binders), a trigger-hygiene
optimization that does not change the modeled semantics.

**Slicing** `xs[lo:hi]` (step 1): both bounds clamp to `[0, k]` after
negative normalization; an inverted range is empty; never an error.
`PySlice` is definitionally this function.

**Builtins.** `len`, `abs`, 2-arg `min`/`max` are the mathematical
functions. 1-arg `min`/`max` over a list require nonemptiness
(`err(ValueError)` otherwise ↔ `PySeqMax.requires`). `sum(xs)` folds left
over an int list with `sum([]) = 0`; `PySum` is snoc-recursive, which is
extensionally equal by associativity of `+`. `sum(g(x) for x in xs)`
evaluates `g` left-to-right over the elements — the fragment's `g` is
side-effect-free (expressions cannot write σ), so the order is
unobservable and the `seq(k, i ⇒ …)` model is exact. A filter
`[e for x in xs if P]` is the same one-pass skip: each `x` is kept as
`[e]` or dropped as `[]`, then concatenated (`PyFlatten`) so order is
CPython's and omitted elements leave no hole. `sum(e for x in xs if P)`
maps skipped elements to `0` (the identity of `+` on `int`). Eager
`all`/`any` genexps, in specs **and** bodies, lower to `forall`/`exists`
(pure generators, so short-circuit vs full evaluation is unobservable);
a filter becomes a conjunct on the domain.

**Quantifiers in specs.** `forall x in range(a, b) :: P` is bounded
conjunction (empty domain ⇒ true), evaluated in the *enclosing* σ — binder
shadowing of any live name is rejected at admission (a captured binder
would silently change which σ the domain reads; see the binder-capture
guards in the encoder).

**Truthiness** (§7.3) is admitted only for list/str operands in condition
position (`⟦xs⟧ ≠ []`), for `bool`-typed expressions, and rejected
otherwise — CPython's full truthiness lattice is deliberately outside the
fragment.

## 4. Statement rules (selected)

**Assignment** rebinds a local: `σ ⊢ x = e ⇓ σ[x ↦ v]` where `σ ⊢ e ⇓ v`.
Optional-typed targets inject/project through `PyOpt` (`_coerce`); tuple
assignment evaluates the right side fully before binding (Python's
simultaneous semantics — the gcd `a, b = b, a % b` case). Unpacking a
tuple-typed name `a, b = p` projects as `a, b := p.0, p.1` (Dafny does
not unpack a single tuple-typed RHS); arity mismatches are encode-time
errors, matching Python's `ValueError`. Tuple index `p[k]` is a constant
(negative wrap like Python) lowered to a Dafny destructor `p.k` — not
`PyIndex`, which is sequence indexing. Tuple concatenation (`t + u`) is
rejected: Dafny tuples are product types, not sequences.

**append** on an owned-fresh list: `σ ⊢ xs.append(e) ⇓ σ[xs ↦ σ(xs) ⧺ [v]]`.
Admission guarantees no alias observes the mutation, so the Dafny value
update `xs := xs + [v]` simulates it.

**for i in range(a, b)** executes the body with `i = a, a+1, …, b−1`; the
loop variable may not be reassigned (admission). The encoder's
`while i < i_hi` with hoisted bounds is the standard unrolling; hoisting is
sound because the bound expressions are pure and their free names are not
written by the body (admission checks this).

**for x in xs** iterates a **snapshot**: CPython iterates the list object
with a hidden index, and the fragment freezes every name in the iterable
expression for the loop's extent, so no mutation can be observed mid-loop;
the encoder's snapshot + hidden index is then exact.

**assert e**: `err(AssertionError)` if false, no-op if true — lowered to a
Dafny `assert`, so a verified function's asserts are proved never to fire,
while CPython still executes them (they are the proof-hint idiom).

**while / if / return** are standard; loop `#@ invariant` clauses are
proof annotations with no runtime content (loop-head, exit-inclusive).

## 5. The simulation statement

Write `G(f)` for the guard predicate of `f` (deep exact types + executable
requires), `⟦·⟧` for the value translation of §1, and `f_D` for the encoded
Dafny method with its proof obligations discharged.

> **Claim (simulation).** Let `f` be a function the conformance checker
> admits, with `f_D` verified. For every argument vector `a̅` with `G(f)(a̅)`,
> the CPython execution of `f(a̅)` under the island assumptions A1–A7:
>
> **(a)** never raises `IndexError`, `ValueError`, `TypeError`,
> `ZeroDivisionError`, or `AssertionError` from fragment constructs — each
> such transition maps to a discharged proof obligation;
>
> **(b)** terminates — the `decreases` obligations map onto a well-founded
> measure of the big-step derivation;
>
> **(c)** returns a value `v` with `⟦v⟧ = f_D(⟦a̅⟧)`-adjacent in the sense
> that every `ensures` clause, interpreted by the rules of §3 over `v` and
> `a̅`, holds — and `old(x)` refers to the copied-in entry value of `x`.
>
> *Proof sketch.* Induction on the big-step derivation, with one lemma per
> catalog row relating the CPython rule to its lowering (the §3/§4
> selections are the non-trivial lemmas; the preamble functions are
> definitionally the partial-operation rules). Loops use the invariant as
> the induction hypothesis at the Dafny side's loop-head placement. Not
> mechanized; asserted per-construct and checked empirically below.

The guarantee consumed by users is this claim *conjoined with* the guard
theorem (guards decide `G(f)` exactly) and the island assumptions (§5) —
that composition is the "precise, honest guarantee" sentence of the README.

## 6. Validation status per construct

Every row is exercised by the differential harness on the corpus
(`veripy difftest`, Hypothesis-driven, CPython vs the Dafny-to-Python
translation of the *same* stub the prover saw).

| construct | rule | lowering | differential coverage |
| --- | --- | --- | --- |
| `//`, `%` | §3 floor | `PyFloorDiv`/`PyMod` | sign matrix, corpus (gcd, is_prime) |
| negative index | §3 index | `PyIndex` | corpus (is_palindrome) + unit |
| slices | §3 slice | `PySlice` | corpus (rolling_max, below_zero) |
| 1-arg min/max | §3 builtins | `PySeqMax/Min` (requires) | corpus (max_element, rolling_max) |
| `sum`, genexp folds | §3 builtins | `PySum` (+ `seq` map; filter → `else 0`) | corpus (below_zero, sum_squares) + unit |
| filtered list comps | §3 comps | `PyFlatten` of 0/1-element seqs | unit |
| eager `all`/`any` genexp | §3 folds | Dafny `forall`/`exists` (body and spec) | unit |
| Optionals | §1/§4 assign | `PyOpt` + coercions | corpus (rolling_max) |
| list build | §4 append | `⧺` under ownership | corpus (incr_list, intersperse) |
| for-range / for-each | §4 loops | hoisted while / snapshot | corpus-wide |
| `break` / `continue` | §4 loops | Dafny `break`/`continue`; for-desugar steps the hidden index before `continue` | unit (while cap, range-for skip) |
| tuples / unpack / multi-return | §4 assign | Dafny `(T, U)` products; `p.k` / `a, b := p.0, p.1`; arity checked at encode time | unit (pair return, unpack, Hypothesis) |
| assert | §4 | Dafny `assert` | corpus (rolling_max, below_zero) |
| truthiness §7.3 | §3 | `\|xs\| != 0` | unit |

Constructs outside this table are outside the fragment — the conformance
checker rejects them by construction, which is what keeps this note short.
