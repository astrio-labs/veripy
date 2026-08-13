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

## lemmapy-benchmark (RQ4 and the headline)

The native benchmark is **lemmapy-benchmark** ([BENCHMARK.md](BENCHMARK.md)): tasks
are annotated-Python modules scored on the assurance ladder (gate → hunt →
mutant panel → encode → prove → fidelity), with **spec strength measured
mechanically** via deterministic mutant kill rates — a dimension no
skeleton-completion benchmark has. Exam variants derive from the golden
corpus (spec-writing, proof-repair, debugging), and rungs R3–R5 are
backend-parameterized: a future Lean backend gets a second prove/fidelity
column over identical tasks, the comparison only a multi-backend toolchain
can make.

**Positioning.** LemmaScript's benchmark (and its runner) is competitor
infrastructure; we do not build on it. It remains useful only as a
difficulty-calibration reference. A cross-tool "olympics" (OpenJML, Verus,
Frama-C, …) is out of scope — competitor-authored comparisons cap their own
credibility (that is VerifyThis/SV-COMP territory, which works because of
neutral governance) — but benchmark task *contracts* are source-language-
neutral and can be published as a portable spec suite others port to their
tools.

**External baselines.** [DafnyBench](https://github.com/sun-wendy/DafnyBench)
and [MBPP-DFY](https://github.com/Mondego/dafny-synthesis) stay as public
comparability anchors for the proof-repair exam (numbers reported side by
side, never averaged; both public-since-2024, so contamination is assumed
and stated). The benchmark's own tasks are freshly authored/adapted with
per-task license metadata; the golden corpus is the held-out set, and any
tuning happens on derived exams over a disjoint task split.

**Metrics.** Ladder height distribution; spec-strength (mutant kill rate,
survivors adjudicated); for agent exams: autonomy rate (tasks restored to
full height with zero human edits), iterations and tokens per task.

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
