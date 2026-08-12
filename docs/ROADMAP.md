# Roadmap

> Milestones are gated on **exit criteria, not dates** — this is a research project. Ordering within a milestone is flexible; ordering across milestones is not, except that M0 deliberately runs in parallel with early M1. Scope details for each item live in [ARCHITECTURE.md](ARCHITECTURE.md); § references below point to its soundness-design sections.

## M0 — Spec surface + runtime checking (parallel, weeks-scale)

Prove the spec surface and gather fragment evidence *before* any prover integration.

- [x] `#@` spec grammar v0 ([SPEC-GRAMMAR.md](SPEC-GRAMMAR.md)): `requires` / `ensures` / `invariant` / `decreases`, ghost `forall` / `exists` / `old()` / `result` (`mutates` / `extern` reserved, not yet in grammar)
- [ ] Spec parser: parse ✅, name-resolve against basedpyright (v0 uses scope-approximate resolution), type-check spec expressions
- [x] Compile the same specs to CrossHair / icontract runtime checks (`lemmapy emit`); CrossHair finds counterexamples from specs alone
- [x] Corpus study, initial run: `lemmapy survey` (read-only AST rule pass, no type info yet) over black/attrs/rich — results and caveats in [CORPUS-RESULTS.md](CORPUS-RESULTS.md); repeat with basedpyright-backed rules and a broader corpus

**Exit criteria:** specs execute as runtime contracts on real code with counterexamples produced; fragment-coverage numbers exist for ≥ a handful of typed OSS repos; the grammar has survived contact with real functions without redesign.

**De-risks:** spec surface DX (the biggest product bet) and fragment scope (the biggest research bet) — both cheaply, before the encoder exists.

## M1 — Verified core (v1, mandatory)

The end-to-end pipeline on the v1 fragment. All four soundness layers present from the first release — none is optional ([ARCHITECTURE.md §2](ARCHITECTURE.md)).

- [ ] Conformance checker: basedpyright strict + allowlist AST pass + ownership dataflow (§3)
- [ ] Fragment IR (thin) + Dafny encoder: two-file output (regenerated stub + additions-only proof file)
- [ ] Versioned Dafny preamble: `PyMod` / `PyFloorDiv`, `PyIndex` / `PySlice`, `Truthy_*`, `Option`, container/str models — with lemmas and its own differential test corpus
- [ ] Guard generator: deep exact-type checks, executable preconditions, copy-in, trusted-caller elision, blame errors (§4)
- [ ] Island integrity hardening + assumptions A1–A7 in the verification report (§5)
- [ ] Verifier driver: failure mapping back to Python source; verification report (per-boundary assumed clauses, trusted-contract counts, guard modes)
- [ ] Translation-validation harness in CI: `dafny translate py` + Hypothesis differential loop (§6)
- [ ] Fragment semantics note: big-step semantics for the fragment + simulation statement (paper, not mechanized)

**Exit criteria:** a fixed benchmark suite of spec'd functions (HumanEval/MBPP-style + a named-algorithms set) verifies end-to-end; guards demonstrably stop the §1 attack gallery (`json.loads`, `cast`, `EvilList`, mock-patching); the differential harness runs on every PR and has caught at least one seeded encoder bug.

## M2 — Agent loop + DX

The differentiating layer: proofs that finish themselves, and rejections that teach.

- [ ] Structured failure output from the verifier driver (obligation, span, counterexample) — the agent interface
- [ ] LLM proof-repair loop: read failures, edit proof file only, re-verify, iterate; M0 counterexamples fed in as test cases
- [ ] Tune the loop against the [LemmaScript Dafny benchmark](https://github.com/midspiral/lemmascript-dafny-benchmark) (33 proof-completion tasks, MIT) using its runner and validator discipline (additions-only, contracts untouched, no `assume`/axioms, pinned Dafny) — works before our encoder exists, so this can start alongside M0
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
