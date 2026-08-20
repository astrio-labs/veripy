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
      (Dafny already lowered it; survey no longer counts a bare `assert`
      as a miss, Lean rejects it loudly naming Dafny. Non-literal
      messages still rejected — they have side effects.)

### Tier 2 preamble (the real volume — `U-METHOD`)

- [x] `str` methods (`split` / `join` / `find` / `strip` / …), ASCII or
      exact-match `PyStr*` models; Unicode-table methods rejected
- [x] `sorted` (permutation + order; stability only on demand)
      (`sorted(xs)` on `list[int]` as `PySorted`; no `key=` / `reverse=` /
      `list[str]` — Dafny seq `<` is prefix order, Python str `<` is lex)
- [x] `str(int)` / `int(str)` with parse VCs
      (one positional arg; bool is a disjoint sort; f-string int
      interpolation stays rejected — Lean has no strings)
- [ ] A small `math` subset

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
