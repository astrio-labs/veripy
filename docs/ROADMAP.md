# Roadmap

> Gated on **exit criteria, not dates**. This file is local planning
> ([`.gitignore`](../.gitignore)); the soundness design lives in
> [ARCHITECTURE.md](ARCHITECTURE.md). The v1 island (specs, encoder,
> guards, difftest, agent loop, exams) is done. What remains is two
> production bars that do not share a finish line.

Admit nothing because it would be nice; admit it because it wins the
rule in [How we decide](#how-we-decide).

---

## How we decide

A construct joins the encoder only if all four hold:

1. **A fire-count on the target corpus.** Typed `veripy survey` (type
   gate on) over the code we actually want verified — greenfield agent
   traces for Bar A, a stratified sample of the service for Bar B.
   Untyped `U-METHOD` is not a vote ([CORPUS-RESULTS.md](CORPUS-RESULTS.md)).
2. **A CPython-faithful lowering** plus a `veripy difftest` cell. No
   cell → no admit. Silent approximation is a soundness bug.
3. **SMT still discharges typical specs**, or the sidecar/whitelist
   story is explicit. If automation dies (IEEE `float`, bit-precise
   FP), veto or put it behind an `#@ assume …` that the report surfaces.
4. **A rejection diagnostic with a rewrite.** “Outside the fragment
   because X, try Y.” If we cannot name Y, we are not ready for an
   agent loop.

Re-run survey after every slice. The next row is whatever still
dominates **on the open bar**, not on HumanEval.

**Permanent veto** until a new research track (do not queue these as
encoder slices): `eval` / `cast` / `# type: ignore`, inheritance/C3,
user dunders, `async` as real interleaving, `yield` as a coroutine,
observable dict-iteration order, IEEE `float`. Those are architecture
changes. Detect and reject; never silent.

Do not expand Bar B to “look prod” before Bar A’s `#@ extern` exists.

---

## Bar A — greenfield product (next)

Meaning: agents write the new system; **business logic is in-fragment
and verified**; HTTP, DB, files, ORM sit behind `#@ extern` and guards.
We never claim “the service is verified.” We claim “these modules are,
modulo N trusted contracts.”

Lean parity is not required for this bar. Dafny-only is enough if
Python remains the artifact.

**Done looks like:** an agent can generate a new service whose
pure/typed helpers sit near the HumanEval in-fragment band, and the
rest is mostly `extern`/IO. Guard overhead is measured. Trusted-contract
count is visible. Classes, `async`, and IEEE float stay refused.

### Close the design catalog already written ([ARCHITECTURE.md §7](ARCHITECTURE.md))

- [x] Tuples / multiple returns / unpacking with arity VCs
- [x] `break` / `continue`
- [x] Full comprehensions + eager `all` / `any` / `sum` genexp folds
      (single generator; nested `for` still rejected)
- [x] `for x in xs` snapshot iteration as first-class
      (`for a, b in pairs` over `list[tuple[…]]`; string iteration still
      rejected — Python yields `str`, Dafny would yield `char`)

### Cheap coverage (survey’s admittable peak)

- [x] f-strings (`T-FSTRING`)
      (str interpolations only; format specs / `!s`/`!r`/`!a` / int
      interpolation still rejected — `str(int)` is a later row)
- [x] Walrus `:=`
      (always-evaluated positions only; `and`/`or`, later chained-
      comparison operands, if-expr branches, comprehensions, and specs
      still rejected — Dafny cannot assign in an expression, and
      hoisting those would ignore short-circuit)
- [x] `assert` as a VC, uniformly
      (both backends lower it now: Dafny always did, and Lean makes each
      assert its own theorem — proved, never assumed. Loop-free asserts
      carry their path conditions, nesting, and preceding locals; an
      assert at the top level of a `for` body — before the accumulator
      is updated — is discharged under the invariant at that iteration
      and then rides into the preservation step, Dafny's
      prove-then-assume. Still rejected by Lean, each being a position
      whose obligation cannot be placed from the loop-head state: an
      assert AFTER the accumulator is updated, one nested under a
      branch inside a loop body, one in a `while` body, and one in an
      early-return search loop. Non-literal messages still rejected —
      they have side effects.)

### Tier 2 preamble (the real volume — `U-METHOD`)

- [x] `str` methods (`split` / `join` / `find` / `strip` / …), ASCII or
      exact-match `PyStr*` models; Unicode-table methods rejected
- [x] `sorted` (permutation + order; stability only on demand)
      (`sorted(xs)` on `list[int]` as `PySorted`; no `key=` / `reverse=` /
      `list[str]` — Dafny seq `<` is prefix order, Python str `<` is lex)
- [x] `str(int)` / `int(str)` with parse VCs
      (one positional arg; bool is a disjoint sort; f-string int
      interpolation stays rejected — Lean has no strings)
- [x] A small `math` subset
  ```
  (`math.gcd` / `factorial` / `isqrt` on ints; IEEE `float` still vetoed)
  ```

### Data a product actually uses

- [ ] Homogeneous `dict` / `set` with hashable value-typed keys
      (reject observable iteration-order dependence; offer `sorted(d)`)
- [ ] Frozen dataclasses as values (`replace` → datatype update)

### Intentional failure (v1.5, [§7.4](ARCHITECTURE.md))

- [ ] `raise` + `Outcome<T>` / Dafny `:-`; finite `except E`; no bare
      `except` / `BaseException`. v1 still proves absence; this is for
      APIs that return errors.

### What makes it a product, not a demo

- [ ] **`#@ extern` (Tier 3)** — typed-but-unverified callees, trusted
      stub, report “verified modulo N”, optional runtime check. Load-bearing
      for Bar A. Without it every call out of the island is a fragment miss.
- [ ] Verified → verified imports (Tier 1)
- [ ] `#@ mutates` *inside* the island only; exported guarded entry
      points stay functional (copy-in, no copy-out)

### Soundness debt that Bar A still owes

- [ ] Full [§3.2](ARCHITECTURE.md) ownership if indexed assignment /
      in-place helpers are admitted (today: admission by exclusion)
- [ ] RQ3: guard overhead per [§4.4](ARCHITECTURE.md) cost-ladder rung
- [ ] Wire the type gate into `veripy survey` so `U-*` fires are honest
- [ ] Thin fragment IR (still a design commitment; Dafny encoder is the
      authority today)
- [ ] Nightly coverage-guided long `veripy difftest` (CI already runs
      the shallow harness on every PR)
- [ ] Batch proof / type-gate results wired into `veripy lsp`
      ([EDITOR.md](EDITOR.md))

Preamble promotion of the divisibility lemma pack stays **deferred**
while the proof-repair exam depends on those lemmas being absent
(`test_sidecar_is_load_bearing`).

The interface-ablation study ([EVALUATION.md](EVALUATION.md)) is
deferred; it is not fragment work.

---

## Bar B — existing Python services (after Bar A’s extern)

Meaning: point VeriPy at FastAPI/Django/httpx-shaped code and certify
**named modules**, not the whole process.

This bar is **not** “N more catalog rows until coverage is 80%.” Survey
is 3–23% of functions in typed OSS; the top fires are attribute stores,
inheritance, unmodeled methods, and unmodeled calls. Closing f-strings
does not verify `pydantic`.

**Done looks like:** named modules certified, every extern listed, the
guard theorem intact. Mixed-mode forever. We do not say “this production
service is verified.”

Depends on Bar A’s `#@ extern`. Then:

- [ ] Frozen dataclasses / simple classes **without inheritance** (value
      objects). No C3, no user dunders, no metaclasses.
- [ ] In-place mutation under full ownership: `#@ mutates`, indexed
      assignment, affine store. Otherwise brownfield lists are all
      rebuilds and nobody annotates the service.
- [ ] `try/except` as `Outcome` (same slice as Bar A intentional
      failure). `with` only for a tiny allowlist; I/O stays extern.
- [ ] Open-ended curated preamble: stdlib and framework models, added
      one function at a time under [How we decide](#how-we-decide). This
      queue does not terminate.

**Still refused (not Bar B work items):** inheritance, metaclasses,
decorator function-surgery, `async` runtime, reflection.

---

## v2 — Research track (not Bar A/B slices)

- [ ] Behavioral subtyping via Dafny traits (single inheritance)
- [ ] Generators as verified state machines
- [ ] Sequentializable-async carve-out
- [ ] Mechanized fragment semantics in Lean (also unlocks a Lean /
      shared-IR backend)
- [ ] Proof of the gradual-verification target theorem ([§4.5](ARCHITECTURE.md))
      over the fragment semantics
- [ ] `#@ assume idealized-reals` for `float`, always a report caveat,
      never IEEE

The Lean backend remains a **strict subset** of the Dafny fragment: if
Dafny would accept a construct and Lean cannot, Lean must fail loudly.

---

## Lean track

A shallow functional embedding: each admitted function becomes a Lean
definition, each clause a theorem, and every artifact ends with
`#print axioms` so a proof leaning on anything outside
`{propext, Quot.sound, Classical.choice}` is reported as
`axiom-footprint` rather than counted. `sorry` and `admit` are the
same axiom underneath, and the check catches both **transitively**.

Loops compile to fuel recursion on `Nat` (structurally terminating, so
no `termination_by`); the invariant becomes a generated `Prop` and the
induction theorem's inductive step **is** the preservation VC.

### Where it actually stands

Measured on the contact corpus, not estimated — re-run before quoting:

| | |
|---|---|
| contact corpus under Lean | **14/22** (`he_35`, `he_42`, `he_52`, `he_60`, `he_49`, `he_13`, `he_31`, `mbpp_sum_squares`, `he_3`, `he_5`, `he_43`, `he_40`, `he_48`, `he_30`) — `he_43` now EXCEEDS Dafny, whose fragment lacks `enumerate` |
| prelude | `lean-0.12` (`Count_filter_of_pos`: counting survives a filter the element passes — the filtered-comprehension class; `IntBexDec` stays the nested-search spine) |
| slices landed | P2 1–20, P3 (sidecar channel) |
| `.proofs.lean` packs in existence | **4** (`he_60`: `GaussStep`; `he_49`: `ModMulLeft` + `PowStepTwo`; `he_13`: `EuclidStepAll` + `FmodCongr`; `he_31`: `ModPredOne` (with a Dafny twin, the first task packed under BOTH provers) — all kernel-checked, clean axiom footprints) |

`he_60` is the first while-loop task with a nonlinear postcondition
proved end to end, and it took the full chain: the pack, the
floor-division bridge, the corrected fuel, and a post-loop
`assert i == n + 1` stating the exit value (slice 20) — proved from
the invariant plus the negated condition, then substituted into the
spec proof so the atom `(i-1)*i` collapses to `n*(n+1)`. The assert
is a runtime check in CPython and a VC in Dafny, so the source stays
one program with three readings.

Per-task first blockers (clearing one reveals the next, so this is a
work list and not a countdown):

| blocker | tasks |
|---|---|
| DP / indexed assignment — **cut by decision** | `mbpp_402`, `mbpp_620`, `mbpp_247` (2-D table), `mbpp_149` (dp array) |
| `int \| None` accumulator — a real fragment addition, not a body-shape issue (earlier table binned it by its first error) | `he_9` |
| `dict` | `mbpp_885` (also `sorted`), `mbpp_97` (also nested comprehension) |
| `sorted` | `he_34` |

The earlier revision of this table grouped `mbpp_247`, `mbpp_885`, and
`mbpp_97` under `str` parameters and `mbpp_149` under "two loops" —
each was binned by its first error message. Reading the sources put
`mbpp_247` and `mbpp_149` in the cut DP class and the other two behind
`dict`, which no slice has touched. `str` was a one-task cluster, not
four, and slice 27 cleared it (slice 28 then cleared `he_30`'s
filtered comprehension: the identity filter is `List.filter`,
membership quantifiers range over elements, and count preservation
rides `Count_filter_of_pos` at the emitted predicate): a `str` parameter is its code-point
sequence (`List Int`), faithful because the admitted operations —
`len`, and comparisons in which every operand is an indexed character
— cannot tell a string from its code points (Python orders characters
by code point). Everything else on a `str`, ghost positions included,
is rejected rather than mistranslated. The same slice added the mirror
license: `xs[len(xs) - 1 - i]` is structurally in bounds wherever `i`
is.

The five tasks that report *"a loop function must be exactly `acc =
init; for ...: ...; return expr`"* are **five different causes sharing
one message**, two of them the cut DP tasks. Read the source before
grouping them.

### Semantics measured the hard way

Each of these was believed otherwise until it was checked:

- Python `//` and `%` are `Int.fdiv`/`Int.fmod`, **not** ediv/emod.
  `emod` agrees only for positive divisors, so a positive-divisor test
  suite never catches it. The differential suite pins all four sign
  combinations.
- Core Lean has **no `ring`**. Polynomial identities are proved by
  rewriting to normal form and letting omega treat `i * i` as an atom.
- The fuel model needs a **stronger measure than Dafny's `decreases`**:
  `while i <= n` needs `n - i + 1`, not `n - i`.
- Tuple assignment is simultaneous; consecutive statements are
  sequential. Opposite semantics, both modelled.

### The recurring bug, and the rule that catches it

Six findings in the encoder have had one root cause, and the fifth and
sixth landed on code written in response to the one before. The last
one **certified a program CPython crashes on**: `s = s + 1; assert s
== i` verified `ok`, and the runtime-true `assert s == i + 1` was
rejected.

The mechanism is always a *convenience lift* — moving a construct out
of its context so downstream code stays simple — and the lift is what
discards the context that made the obligation correct.

> **When a construct is lifted out of its context, it carries its full
> context — the path that reaches it, the locals bound at it, the
> mutations that precede it, the nesting it sits in, and whether its
> position is decidable — or the lift REFUSES the contexts it cannot
> carry.**

Refusing what cannot be reconstructed is the half that separates
incompleteness from certifying a crash. It takes a different concrete
form on each path, and the two are **not** interchangeable:

- **Loop-free bodies.** `_collect_asserts` must walk the same
  control-flow shape `_body_expr` compiles. Anywhere the two disagree
  about what guards a statement is a bug by construction — that is
  where the implicit-else and local-substitution findings came from.
- **Loop bodies.** Neither of those helpers goes near a loop body:
  `_collect_asserts` steps *over* `For`/`While` (dropping only the
  names they rebind) and `_body_expr` has no `For` branch at all. The
  lift lives in `_split_loop`, and `_touches_acc` is what keeps it
  honest — an assert may be lifted only from a position where the
  accumulator still holds its loop-head value, because that is the
  state the obligation is stated in. **This is the guard to preserve
  when loop-assert lifting is extended**; it is the one that catches
  the crash case above.

### Next, by measured value

1. `str` parameters — the largest reachable cluster (4 tasks)
2. Lemma packs for the three pack-stage tasks — the only ones where a
   single piece of work moves the count. Packs are **author-written**
   and derived independently of the Dafny decomposition (Lean's
   automation differs enough that mirroring would misstate difficulty);
   engine packs are scored by the prover, never by similarity to ours.
3. List-slice / mapped-`PySum` equality — what makes slice 18's
   `assert`-as-hint actually pay off (`he_3`, `he_9`,
   `mbpp_sum_squares` all state slice-extension facts)
4. Nested loops (2 tasks)
5. P4: `--backend lean` through the exams, then triple adjudication

---

## Backend watchpoints

Dafny-first is a decision with tripwires, not a dogma. Re-open if:

1. Laurel stabilizes (versioning + a documented Python fragment)
2. Public automation evidence matches Dafny on program-verification
   workloads
3. Limited-local-mutation lands and Dafny’s heap encoding is the
   bottleneck
4. AWS ships developer/agent-facing DX on Strata — interop vs compete

The thin fragment IR exists so a tripwire is an emitter, not a rewrite.

---

## Non-goals

From [ARCHITECTURE.md §9](ARCHITECTURE.md): full CPython semantics;
`float` verification without an explicit assume; behavior under runtime
patching of island definitions, `ctypes`, or concurrent mutation
(A1–A3); soundness past asynchronous exceptions or resource exhaustion
(A5); correctness of Tier 3 extern contracts (trusted, counted,
optionally runtime-checked). Each non-goal is detected and rejected,
guarded, or stated — never silent.
