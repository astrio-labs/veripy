# Evaluation

> **Status: partial draft.** The proof-completion benchmark family (this document's core) is designed; the fragment-coverage corpus selection, success thresholds, and guard-overhead methodology are sketched but **not yet decided** — marked *open* below. Companion to the roadmap (which milestone produces what) and [ARCHITECTURE.md](ARCHITECTURE.md) (what the measurements are claims about).

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

Run the conformance rules read-only over typed OSS repos; report the fraction of functions/LOC accepted and rule-fire frequencies (which drive v1.5 admission priorities, per the roadmap). Candidate corpora: `black`, `attrs`, `mypy`, `rich`, plus a stratified sample of strict-mode-clean packages. *(Open: final repo list, selection criteria, and what coverage number constitutes "enough" for the greenfield thesis — note the thesis frames the fragment as a generation target, so brownfield coverage is context, not a gate.)*

## Guard overhead (RQ3)

Per cost-ladder rung ([ARCHITECTURE.md §4.4](ARCHITECTURE.md)): micro-benchmarks per boundary crossing (beartype/typeguard-style methodology) and macro-benchmarks on the RQ2 suite with guards on/off, reported against the Takikawa et al. warning about gradual-typing overheads. *(Open: workload selection and acceptable-overhead thresholds per rung.)*

---

## Hygiene rules (global)

1. **Dev/held-out separation is absolute:** anything tuned on is dev; the held-out suite is frozen, versioned, and touched only to run.
2. **Task shapes are never averaged:** skeleton-completion, annotation-restoration, and end-to-end numbers are reported separately.
3. **Pinned toolchain:** Dafny, Z3, basedpyright, and CPython versions pinned per benchmark version; version bumps re-baseline.
4. **Append-only ledgers:** every trial recorded (model, prompt version, tokens, wall-clock, outcome), following the LemmaScript runner's practice.
5. **Contamination is assumed for public sets** and stated wherever their numbers appear.

## Measured proof-repair runs (August 2026) — the M2 exit metric

**Setup.** `lemmapy benchmark --exam proof-repair --engine claude` over the
sidecar-bearing golden corpus. Engine: headless `claude -p` (claude CLI
2.1.193, default model configuration), **all tools denied and an isolated
empty working directory** (invocation pinned by unit tests, including the
argument ordering); budget 4 iterations, 60 s verify per attempt; Dafny
4.11.0. The metric: proof-completion rate with no human edits, restoration
re-earned through the sidecar whitelist and the prover.

### Run 1 — roster n=1 (gcd)

**1/1 restored, 2 iterations.** The engine-authored pack was independent
of the golden proof: eight lemmas under a different decomposition
(`DivModRel`/`MulMono`/`MulDivZero`/`MulMod`/`AddMod`/`SubMod`/
`EuclidStepOne`), sharing only the `EuclidStepAll` entry point the frozen
`#@ proof` clause names. Artifact:
[exam-artifacts/gcd-engine-pack-2026-08.dfy](exam-artifacts/gcd-engine-pack-2026-08.dfy).

### Run 2 — roster n=2 (gcd, modp), after slice 7 grew the corpus (superseded by Run 3)

**1/2 restored (50%) at the default 4-iteration budget.**

| task | restored | iterations | note |
| --- | --- | --- | --- |
| gcd | yes | 1 | independent **5-lemma** pack — *smaller than the golden 8* ([artifact](exam-artifacts/gcd-engine-pack-2026-08b.dfy)) |
| modp | no | 4 (budget) | independent near-miss: a `ModIdentity`/`ModPeriodic` grounding whose own sidecar postconditions did not prove ([unverified attempt](exam-artifacts/modp-engine-unverified-attempt-2026-08.dfy)) |

A follow-up probe at an 8-iteration budget was **inconclusive for a
measured reason**: the repair request embeds the attempt history, and by
iteration 3 the prompt had grown enough that the engine call exceeded its
own 600 s wall. History capping/summarization in the loop is recorded as
follow-on work; until then, reported numbers are at the default budget.

The two-task roster already discriminates: gcd's divisibility argument
(inductive, linear steps) restores easily — twice, via two different
proofs, once smaller than the human one — while modp's nonlinear
mod-multiplication congruence does not restore within budget. Roster
growth remains the highest-leverage improvement to this metric.

### Roster n=6, and the experiment harness (late August 2026)

Four more tasks gained load-bearing sidecars — `below_zero` (`SliceSnoc`),
`rolling_max` (`SeqMaxDominates`), `sum_squares` (`SumNonNeg`), and
`is_prime` (rewritten to sqrt-bounded trial division with the full iff
spec, reusing gcd's divisibility family) — joining `gcd` and `modp` for a
six-task roster.

Each was **screened before adoption**: the strengthened spec had to fail
to prove *without* its pack. A task Z3 proves from its invariants alone
makes an exam row that measures nothing, so the screen is permanent, as
`test_sidecar_is_load_bearing` over the roster and as `lemmapy benchmark
--screen` for candidates. (For the same reason the divisibility family is
deliberately **not** promoted into the preamble while the exam depends on
those lemmas being absent.)

**Correction (2026-08-14): the automated screen was vacuous until now, and
this paragraph overstated it.** It dropped the sidecar and asserted the
task no longer verified — but it left the `#@ proof` clauses in the source,
so the *encoder* rejected the file (`unknown lemma 'X'`) before the prover
ran. That happens for every task, load-bearing or not, so the assertion
could not fail. The screen now strips the clauses too and requires a
genuine **prover** failure, with a third verdict — `inconclusive` — for
exactly the state the old one was silently reporting as a pass. Re-run
against the roster on the corrected screen: **6/6 load-bearing**
(`postcondition` for below_zero, is_prime, rolling_max, sum_squares;
`timeout` for gcd and modp), so the numbers above stand. The manual
pre-adoption screening was real; it was the standing tripwire that was
not.

Runs are now driven by `lemmapy experiment`, which executes an exam as a
(task × engine × arm × trial) matrix against an append-only JSONL ledger:
resumable, with the run's git rev and tool versions in the header, three
arms (full loop / one-shot / feedback-ablated) to separate what the loop
contributes from what the model already knows, and per-proposal
whitelist-rejection telemetry. Rates are reported with Wilson intervals —
k/n at these trial counts is not a defensible point estimate on its own.

### Run 3 — roster n=6 (2026-08-14), the current figure

**4/6 restored at the default 4-iteration budget** — but the denominator
needs reading, because one task never produced a measurement at all:

| task | restored | iterations | note |
| --- | --- | --- | --- |
| below_zero | yes | 2 | |
| gcd | yes | 1 | |
| is_prime | yes | 2 | |
| sum_squares | yes | 1 | |
| modp | **no** | 4 (budget) | genuine failure: nonlinear mod-multiplication congruence not reached within budget |
| rolling_max | **unmeasured** | 3 | the engine call exceeded its own 600 s wall — a HARNESS failure, not a statement about proof-completion |

So: **4/5 = 80% (95% Wilson CI 38–96%) of tasks that produced a
measurement**, or 4/6 = 67% (95% Wilson CI 30–90%) if the harness failure
is counted against the engine. Both are stated because silently choosing
the flattering denominator is exactly the kind of thing the trivial-spec
floor exists to prevent elsewhere. `rolling_max` should be re-run before
either number is quoted.

Read the intervals, not the point estimates: at n=6 the data is compatible
with a true rate anywhere from ~a third to ~all, so this run **cannot**
distinguish a good repair loop from a mediocre one. It is a floor showing
the loop works end-to-end on real proofs, not a rate. Narrowing it needs
roster growth and repeated trials (the matrix arms above), not a better
sentence about six tasks.

Note the prompt-budget fix was already in effect for this run (prior
proposals digested, the duplicate sidecar copy removed), so it reduced
prompt growth without eliminating the 600 s wall on the hardest task —
the engine's own thinking time, not just prompt size, is the binding
constraint there.

**What the run taught beyond the number.** It produced 15 unclassified
failure records, and every one was a Dafny *resolution* error in an
engine-written sidecar (`unresolved identifier: PyMaxSeq`, `wrong number
of arguments`, `incorrect argument type`). That is the most common failure
the repair loop actually hits, it was unlabelled, and it needs the
opposite instruction from the obligation kinds it resembled: the sidecar
did not typecheck, so the proof was never attempted and strengthening it
is wrong. It gets its own `resolution` kind in the failure taxonomy —
shipping separately in the taxonomy PR, so on this revision the
classification is not yet available and these still arrive as `unknown`.

**Methodology notes — two invalid runs preceded the first measurement, in
opposite directions, and both are part of the record:**

1. **Retrieval contamination (score too good).** The first attempt used
   the engine's default configuration: headless `claude -p` with tool
   access, working directory at the repository root. The agent *found the
   answer key* — the identical golden pack at
   `examples/contact/he_humaneval_13.proofs.dfy` — and returned it
   verbatim (comment-for-comment identical; caught because all eight
   helper-lemma names matched, which independent derivation would not
   produce). A perfect score measuring retrieval, not proof completion.
   Consequence: the engine denies all tools and runs from an isolated
   empty directory, pinned by unit tests. Any exam whose engine is
   agentic must assume it will look for the answer key.
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
