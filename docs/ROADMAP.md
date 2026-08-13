# Roadmap

> Milestones are gated on **exit criteria, not dates** — this is a research project. Ordering within a milestone is flexible; ordering across milestones is not, except that M0 deliberately runs in parallel with early M1. Scope details for each item live in [ARCHITECTURE.md](ARCHITECTURE.md); § references below point to its soundness-design sections.

## M0 — Spec surface + runtime checking (parallel, weeks-scale)

Prove the spec surface and gather fragment evidence *before* any prover integration.

- [x] `#@` spec grammar — **v0.1, frozen** after the grammar-contact exercise ([SPEC-GRAMMAR.md](SPEC-GRAMMAR.md), [GRAMMAR-CONTACT.md](GRAMMAR-CONTACT.md)): `requires` / `ensures` / `invariant` / `decreases`, `forall` / `exists` / `old()` / `result` / `<==>` (`mutates` / `extern` reserved)
- [x] Spec parser: parse ✅; `lemmapy check` gates files on basedpyright strict (the A7 first pass) ✅; spec-expression resolution against the checker's symbol table **re-scoped to M1**, where it lives inside the conformance checker (scope-approximate resolution held up across the 20-task contact corpus)
- [x] Compile the same specs to CrossHair / icontract runtime checks (`lemmapy emit`, `lemmapy hunt`); CrossHair finds counterexamples from specs alone
- [x] Corpus study: `lemmapy survey` (read-only AST rule pass, no type info yet) over nine typed OSS repos plus the HumanEval/MBPP greenfield contrast — results and caveats in [CORPUS-RESULTS.md](CORPUS-RESULTS.md); repeat with basedpyright-backed rules in M1

**Exit criteria:** specs execute as runtime contracts on real code with counterexamples produced; fragment-coverage numbers exist for ≥ a handful of typed OSS repos; the grammar has survived contact with real functions without redesign.

**Status: exit criteria met (August 2026)** — 20-task contact corpus with mutation-tested specs and adversarial verification ([GRAMMAR-CONTACT.md](GRAMMAR-CONTACT.md)); nine-repo coverage numbers plus the 65% HumanEval / 67% MBPP greenfield contrast; grammar frozen at v0.1 with one additive change (`<==>`).

**De-risks:** spec surface DX (the biggest product bet) and fragment scope (the biggest research bet) — both cheaply, before the encoder exists.

## M1 — Verified core (v1, mandatory)

The end-to-end pipeline on the v1 fragment. All four soundness layers present from the first release — none is optional ([ARCHITECTURE.md §2](ARCHITECTURE.md)).

- [x] Conformance checker: basedpyright strict + allowlist AST pass + ownership dataflow (§3) — `lemmapy check` runs all three by default: spec parse, type gate, and a fragment-conformance dry-run of the Dafny encoder (the single conformance authority, so `check` reports exactly what `verify` would reject — allowlist admission, ownership-lite, builtin-shadow and binder guards — without needing Dafny installed); `--no-fragment` opts out
- [ ] Fragment IR (thin) + Dafny encoder: two-file output (regenerated stub + additions-only proof file) — **slice 1 shipped**: clean-bucket encoder (`lemmapy verify`), single self-contained stub with a STUB END marker (additions-only enforced diff-wise, benchmark-style); 6 functions verified end-to-end incl. loop invariants; seeded clamp bug caught statically with the failure mapped to the Python line. **Slice 3 shipped**: list building — `append` under ownership-lite (§3.2 conservative: fresh, unaliased, not-under-iteration), list literals, filterless comprehensions → `seq(n, i => ...)`, for-each over lists (snapshot + hidden index), §7.3 list truthiness in conditions; `incr_list` and `intersperse` verified (8 functions total). **Slice 4 shipped**: `Optional[T]`/`T | None` → `PyOpt<T>` with narrowing replayed as `.v` well-formedness VCs, `is [not] None`, Some-injection/projection coercions, Python-exact `==`-with-None semantics; slices → clamped `PySlice`; 1-arg `max`/`min` → `PySeqMax`/`PySeqMin` (empty-seq requires = Python's ValueError); Python `assert` lowers to Dafny assert (runtime check + proof hint — the X-ASSERT candidate graduates); index policy: provably-nonneg indices bare for trigger compatibility, PyIndex otherwise; `rolling_max` verified (9 functions total; preamble 0.3). **Slice 6 shipped**: `sum()` folds — `sum(<list[int]>)` and filterless `sum(<genexp over a list>)` → `PySum` (preamble 0.4, snoc-recursive so the established executable-`assert` slice-extension idiom steps running-sum invariants with no new lemma machinery); keyword arguments to encoded builtins now rejected (previously silently dropped — `max(a, b, key=abs)` miscompiled); `below_zero` (HumanEval/3) and `sum_squares` verified (12 functions total, benchmark 12/12 at full ladder, 42/42 mutants killed). The slice's adversarial round closed two verified-but-false name-resolution holes that predate it: any module/parameter/local binding that shadows an encoder-builtin (`len`/`min`/`max`/`abs`/`sum`/`range`/`bool`/`all`/`any`/`old`) is rejected (an unspecced `def sum` used to vanish from the model while call sites encoded as the builtin), and quantifier/comprehension binders that collide with an enclosing binder are rejected (name_overrides silently rewrote the bound variable); `range(...)` keywords rejected at every structural matcher (CPython TypeError, previously read as positional-only)
- [ ] Versioned Dafny preamble: `PyMod` / `PyFloorDiv`, `PyIndex` / `PySlice`, `Truthy_*`, `Option`, container/str models — with lemmas and its own differential test corpus. **v0.4 shipped** (`PyMod`/`PyFloorDiv`/`PyMin`/`PyMax`/`PyAbs`/`PyIndex`/`PySlice`/`PyOpt`/`PySeqMax`/`PySeqMin`/`PySum`). **The divisibility lemma pack shipped** as gcd's proof sidecar (`he_humaneval_13.proofs.dfy`, 8 ghost lemmas grounded in an inductive `MulPositive`) invoked via the new `#@ proof` clause — the designated first proof-additions case, done: gcd VERIFIED with its full maximality spec (10 functions total). Promote the pack to the preamble when a second user appears
- [ ] Guard generator: deep exact-type checks, executable preconditions, copy-in, trusted-caller elision, blame errors (§4)
- [ ] Island integrity hardening + assumptions A1–A7 in the verification report (§5)
- [ ] Verifier driver: failure mapping back to Python source ✅ (slice 1); verification report (per-boundary assumed clauses, trusted-contract counts, guard modes) pending
- [x] Translation-validation harness (§6): `lemmapy difftest` — `dafny translate py` + Hypothesis over typed signatures filtered by executable `#@ requires`, compared across the value adapter; runs in the test suite over the slice-1 targets (incl. unproven gcd — fidelity is orthogonal to proof). Nightly coverage-guided runs and per-entry-point CI budgets pending
- [ ] Fragment semantics note: big-step semantics for the fragment + simulation statement (paper, not mechanized)

**Exit criteria:** a fixed benchmark suite of spec'd functions (HumanEval/MBPP-style + a named-algorithms set) verifies end-to-end; guards demonstrably stop the §1 attack gallery (`json.loads`, `cast`, `EvilList`, mock-patching); the differential harness runs on every PR and has caught at least one seeded encoder bug.

## M2 — Agent loop + DX

The differentiating layer: proofs that finish themselves, and rejections that teach.

- [ ] Structured failure output from the verifier driver (obligation, span, counterexample) — the agent interface
- [ ] LLM proof-repair loop: read failures, edit proof file only, re-verify, iterate; M0 counterexamples fed in as test cases
- [ ] Tune the loop against **benchmark-derived proof-repair exams** ([BENCHMARK.md](BENCHMARK.md)): strip the proof additions from golden tasks and score R4-restoration under frozen specs — our own corpus, our own harness, no competitor infrastructure
- [ ] Diagnostics quality pass: every conformance rejection line-precise with a fixit ("outside the fragment because X, try Y")
- [ ] Editor surface (LSP or equivalent): verified/unverified status per function, spec hovers, rejection diagnostics inline

**Exit criteria:** measured LLM proof-completion rate on the M1 benchmark suite without human edits (the headline DX metric); a newcomer can take an unannotated fragment-conformant function to "verified" using only tool feedback.

## v1.5 — Fragment growth (telemetry-driven)

Admissions ranked by M0/M1 corpus telemetry; expected order per the design docs:

- [ ] `try/except` via `Outcome<T>` + Dafny's `:-` operator (§7.4)
- [ ] Mutable dataclass methods under the ownership rules
- [ ] Broader str surface
- [ ] Validated-source tokens (the O(1) boundary rung, §4.4)
- [ ] Generator carve-out extensions, as telemetry justifies

## v2 — Research track

- [ ] Behavioral subtyping via Dafny traits (single inheritance)
- [ ] Generators as verified state machines
- [ ] Sequentializable-async carve-out
- [ ] Limited-local-mutation extension of the ownership discipline
- [ ] Mechanized fragment semantics in Lean — also unlocks the Lean/shared-IR backend option
- [ ] Proof of the gradual-verification target theorem (§4.5) over the fragment semantics

## Backend watchpoints

Dafny-first is a decision with tripwires, not a dogma. Re-open the backend question if any of these fire:

1. **Laurel stabilizes** — Strata publishes versioning/stability guarantees and a documented Python fragment for external front-ends
2. **Automation evidence** — public benchmarks show Laurel/Strata solver automation competitive with Dafny on program-verification workloads
3. **Fragment outgrows Dafny** — limited-local-mutation lands and Dafny's heap encoding becomes the bottleneck (Laurel's objects + `modifies` support becomes attractive)
4. **AWS ships developer/agent-facing DX on Strata** — reassess positioning overall: interop (emit Laurel) vs. compete

The thin fragment IR in [ARCHITECTURE.md](ARCHITECTURE.md) exists so that acting on a tripwire is an emitter, not a rewrite.

## Non-goals (permanent or long-deferred)

From [ARCHITECTURE.md §9](ARCHITECTURE.md): full CPython semantics; `float` verification in v1 (no sound model that preserves SMT automation); behavior under runtime patching of island definitions, `ctypes`, or concurrent mutation (assumptions A1–A3); soundness past asynchronous exceptions or resource exhaustion (A5); correctness of Tier 3 extern contracts (trusted, counted, optionally runtime-checked). Each non-goal is detected and rejected, guarded, or stated — never silent.

## Evaluation

Four measurements anchor the claims — fragment coverage on typed OSS corpora, the end-to-end verification benchmark, guard overhead per cost-ladder rung, and LLM proof-completion rate. The measurement plan lives in [EVALUATION.md](EVALUATION.md): the proof-completion benchmark family is designed (the LemmaScript Dafny benchmark as dev set, a held-out Python-derived suite as headline, DafnyBench and MBPP-DFY for external comparability); corpus selection and success thresholds are still open.
