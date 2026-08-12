# Evaluation

> **Status: partial draft.** The proof-completion benchmark family (this document's core) is designed; the fragment-coverage corpus selection, success thresholds, and guard-overhead methodology are sketched but **not yet decided** — marked *open* below. Companion to [ROADMAP.md](ROADMAP.md) (which milestone produces what) and [ARCHITECTURE.md](ARCHITECTURE.md) (what the measurements are claims about).

## Research questions

Four measurements anchor the project's claims:

| # | Question | Measurement | Milestone |
| - | --- | --- | --- |
| RQ1 | How much real typed Python falls inside the fragment? | Fragment coverage over typed OSS corpora | M0 |
| RQ2 | Does the pipeline verify real tasks end-to-end? | End-to-end verification benchmark | M1 exit |
| RQ3 | What do the boundary guards cost? | Overhead per §4.4 cost-ladder rung | M1/v1.5 |
| RQ4 | Can LLMs finish the proofs without humans? | Proof-completion rate on the benchmark family below | M2 |

RQ4 is the headline DX metric and gets the most design attention here.

---

## The proof-completion benchmark family (RQ4)

### Shared task format and protocol

All sets in the family use the format proven by the [LemmaScript Dafny benchmark](https://github.com/midspiral/lemmascript-dafny-benchmark):

- **Task:** a `.dfy.gen` skeleton (contracts and bodies, no proofs) to be completed into a verifying `.dfy`.
- **Rules (validator-enforced):** additions-only diff; generated contracts untouched; no `assume`, `{:axiom}`, `{:verify false}`, or other escape hatches; pinned Dafny version (4.11.x, matching the LemmaScript validator).
- **Runner:** the [LemmaScript trial runner](https://github.com/midspiral/lemmascript-dafny-benchmark-runs) — per-run manifests, frozen candidates, full transcripts, append-only trials ledger, token and wall-clock accounting. (License pending upstream; requested from MidSpiral.)
- **Metrics:** pass@k per task; **autonomy rate** (fraction of tasks completed with zero human edits) as the headline number; iterations and tokens per completed proof as cost curves; all broken down per stratum (below).

These rules are identical to the discipline the agent loop's output must satisfy in production ([ARCHITECTURE.md](ARCHITECTURE.md), LLM proof-repair loop) — the benchmark measures the deployed behavior, not a proxy.

### Development set: LemmaScript Dafny benchmark

33 proof-completion tasks derived from LemmaScript (TypeScript) case studies; MIT-licensed including tasks (all 17 upstream repos MIT, verified via `tasks/ATTRIBUTION.md`).

**Role:** tuning only — prompts, iteration strategy, lemma-suggestion heuristics, model selection. Available *now*, before our encoder exists, which decouples M2 development from M1. **Never reported as a held-out result.**

### Held-out headline set: the Python-derived suite

The Python-sourced mirror of the LemmaScript benchmark — same format, rules, and runner; source language is the only variable. Built from our own toolchain's output, so it samples the proof-idiom distribution our users actually face (`PyMod`/`PyFloorDiv`, `Truthy_*`, seq/map container models, `Option` narrowing VCs, bounds VCs from index desugaring). Working name: `<toolchain>-dafny-benchmark` (project name pending).

**Construction pipeline:**

1. **Assemble the source corpus** — annotated Python functions inside the v1 fragment, drawn from: HumanEval+ and MBPP+ tasks (EvalPlus variants, for the stronger test suites), ported VerifyThis competition problems and named algorithms, and a subset of Nagini's example suite (the nearest-precedent comparison). This same corpus's *source side* is the RQ2 end-to-end benchmark — one corpus, two benchmarks.
2. **Write `#@` specs** for each function; specs must be strong enough that the EvalPlus test suites pass under spec-derived Hypothesis strategies (guards against vacuous specs).
3. **Run the front half of the toolchain:** conformance checker must accept; encoder emits the `.dfy.gen` stub. A function the checker rejects is out (and recorded — that's RQ1 telemetry, not benchmark filler).
4. **Package each stub as a task** under the shared format; carry per-task metadata: source problem, fragment features used, lowering-catalog buckets touched.
5. **Write reference solutions** (human or frontier-model, hand-audited) proving solvability; difficulty tiers by added non-blank proof lines, matching the LemmaScript tiering (small 1–10, medium 11–50, large 51–150, very large 151+).
6. **Freeze and version at M1 exit.** After freezing: no tuning against it, no task edits without a version bump, append-only results ledger.

**Stratification — the diagnostic axis.** Tasks are labeled by lowering-catalog bucket ([ARCHITECTURE.md §7](ARCHITECTURE.md)): *clean* lowerings, *exactly-right desugarings* (`PyMod`, slices, truthiness), *curated Tier 2 models* (str/dict/sorted). Per-bucket completion rates turn the benchmark into an encoder diagnostic: a failure cluster on desugaring tasks means the preamble needs stronger lemmas, not that the agent loop is weak.

**Target size:** 40–60 tasks initially, growing with the fragment (each v1.5 admission contributes tasks exercising the new lowering). *(Open: exact size and per-bucket quotas.)*

**Why held-out status is credible:** the LemmaScript set absorbs all tuning; and although the *Python sources* (HumanEval/MBPP) are in every model's training data, the *Dafny artifacts* are freshly generated by our encoder and have never existed publicly — the proof tasks themselves are contamination-resistant.

### External comparability sets: DafnyBench and MBPP-DFY

- **[DafnyBench](https://github.com/sun-wendy/DafnyBench)** (~555 programs; annotation-restoration task): the community-standard number. We report our loop on it for comparability with published results (Formal Disco's Claude and fine-tuned-Qwen baselines). **Caveat:** annotation-restoration is a different task shape from skeleton completion — report side by side, never averaged. Note our loop's Dafny-side moves (proof file only) don't map 1:1 onto DafnyBench's format; we adapt by allowing the loop's full output surface and documenting the adaptation.
- **[MBPP-DFY](https://github.com/Mondego/dafny-synthesis)** (Misu et al.; ~150 MBPP problems as human-written verified Dafny): two roles. (a) External baseline on a well-studied set. (b) **The encoder-tax experiment:** for MBPP problems present in both MBPP-DFY and our suite, compare proof effort on *hand-written* Dafny vs. *our encoder-generated* Dafny for the same problem — a problem-matched measurement of how much harder (or easier) our translation idioms make proving. This isolates the encoder's contribution to proof difficulty from the problem's intrinsic difficulty.
- **Contamination caveat for both:** public since 2024; assume memorization pressure. They anchor comparability; the held-out suite anchors claims.

### The cross-language experiment

Same protocol, validator, and runner across the LemmaScript set (TypeScript-sourced) and our suite (Python-sourced) enables a controlled comparison: *is Dafny generated from Python harder to prove than Dafny generated from TypeScript, and which lowerings account for the difference?* Report per-tier and per-bucket. This is a publishable result independent of the toolchain's headline claims.

---

## End-to-end verification benchmark (RQ2)

The source side of the corpus from step 1 above: annotated Python in, verification report out, per-task. M1's exit criterion is this suite verifying end-to-end (with reference proof files where automation alone is insufficient). Metrics: fraction verified; annotation overhead (spec lines per code line); wall-clock per function. *(Open: pass threshold for M1 exit.)*

## Fragment coverage (RQ1)

Run the conformance rules read-only over typed OSS repos; report the fraction of functions/LOC accepted and rule-fire frequencies (which drive v1.5 admission priorities, per [ROADMAP.md](ROADMAP.md)). Candidate corpora: `black`, `attrs`, `mypy`, `rich`, plus a stratified sample of strict-mode-clean packages. *(Open: final repo list, selection criteria, and what coverage number constitutes "enough" for the greenfield thesis — note the thesis frames the fragment as a generation target, so brownfield coverage is context, not a gate.)*

## Guard overhead (RQ3)

Per cost-ladder rung ([ARCHITECTURE.md §4.4](ARCHITECTURE.md)): micro-benchmarks per boundary crossing (beartype/typeguard-style methodology) and macro-benchmarks on the RQ2 suite with guards on/off, reported against the Takikawa et al. warning about gradual-typing overheads. *(Open: workload selection and acceptable-overhead thresholds per rung.)*

---

## Hygiene rules (global)

1. **Dev/held-out separation is absolute:** anything tuned on is dev; the held-out suite is frozen, versioned, and touched only to run.
2. **Task shapes are never averaged:** skeleton-completion, annotation-restoration, and end-to-end numbers are reported separately.
3. **Pinned toolchain:** Dafny, Z3, basedpyright, and CPython versions pinned per benchmark version; version bumps re-baseline.
4. **Append-only ledgers:** every trial recorded (model, prompt version, tokens, wall-clock, outcome), following the LemmaScript runner's practice.
5. **Contamination is assumed for public sets** and stated wherever their numbers appear.
