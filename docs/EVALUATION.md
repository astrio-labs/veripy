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

## First measured proof-repair run (August 2026) — the M2 exit metric

**Setup.** `lemmapy benchmark --exam proof-repair --engine claude` over the
sidecar-bearing golden corpus (roster: `gcd`, whose maximality ensures needs
an 8-lemma divisibility pack). Engine: headless `claude -p` (claude CLI
2.1.193, default model configuration), **all tools denied and an isolated
empty working directory**; budget 4 iterations, 60 s verify per attempt;
Dafny 4.11.0. Exit criterion measured: proof-completion rate with no human
edits, restoration re-earned through the sidecar whitelist and the prover.

**Result.** **1/1 restored (100%), 2 iterations, no human edits.** The
engine-authored pack is **independent of the golden proof**: eight lemmas
under a different decomposition (`DivModRel`, `MulMono`, `MulDivZero`,
`MulMod`, `AddMod`, `SubMod`, `EuclidStepOne`, `EuclidStepAll`; 130 lines
vs the golden 115), sharing only the `EuclidStepAll` entry point that the
frozen `#@ proof` clause names. The first proposal failed verification and
the structured-failure feedback produced the verified pack on the second
attempt — the loop, not one-shot recall, did the work. The artifact is
preserved at [exam-artifacts/gcd-engine-pack-2026-08.dfy](exam-artifacts/gcd-engine-pack-2026-08.dfy).
Caveat stated plainly: the roster is n=1 today (`gcd` is the corpus's
hardest proof, but one task is one task) — the number's statistical power
grows with every sidecar-bearing task the corpus gains.

**Methodology notes — two invalid runs preceded the measurement, in
opposite directions, and both are part of the record:**

1. **Retrieval contamination (score too good).** The first run used the
   engine's default configuration: headless `claude -p` with tool access,
   working directory at the repository root. The agent *found the answer
   key* — the identical golden pack at
   `examples/contact/he_humaneval_13.proofs.dfy` — and returned it
   verbatim (comment-for-comment identical; caught because all eight
   helper-lemma names matched, which independent derivation would not
   produce). A perfect score measuring retrieval, not proof completion.
   Consequence: the engine now denies all tools and runs from an isolated
   empty directory, and a unit test pins the invocation. Any exam whose
   engine is agentic must assume it will look for the answer key.
2. **Broken invocation (score too bad).** The first hardening attempt put
   the prompt after `--disallowedTools`, a variadic flag that swallowed
   the prompt text as tool-name rules; every iteration errored, scoring
   0/1 for a reason unrelated to proofs. Consequence: the argument
   *ordering* is part of the pinned test, and the tool-denial itself was
   verified by a live probe (an unguessable token file the engine had to
   fail to read — a first probe against `/etc/hosts` was itself invalid,
   since the model can recite that file's first line from world
   knowledge).

The general lesson both directions teach: record the engine invocation
verbatim next to any reported number, and validate the harness with
positive AND negative probes before trusting either a good or a bad score.
