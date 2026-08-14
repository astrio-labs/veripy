# lemmapy-benchmark

> **Status: v0 — runner and 14-task seed corpus shipped.** `lemmapy benchmark`
> runs it; the scorecard below regenerates with `--report`.

## Why not a skeleton-completion benchmark

The obvious move was a proof-completion benchmark in the LemmaScript style:
frozen prover-IR skeletons, additions-only diffs, one verified/failed bit per
task. We deliberately did something else, because that design measures a
prover-adjacent skill in the IR — the source language, the specs' quality,
the runtime semantics, and the toolchain itself never appear. LemmaPy's
product claim is end-to-end (*annotated Python in, assured Python out*), and
its architecture runs one spec surface through **multiple** assurance
mechanisms. The benchmark should measure exactly that.

## The assurance ladder

A task is one annotated-Python module (`task.py`, plus an optional
`task.proofs.dfy` lemma sidecar). Every task is scored by how far it climbs:

| Rung | Name | What it measures |
| --- | --- | --- |
| R0 | **gate** | specs parse; basedpyright strict clean |
| R1 | **hunt** | CrossHair finds no counterexample against the specs |
| R2 | **mutants** | **spec strength**: an auto-generated panel of single-fault mutants (operator swaps, off-by-ones — deterministic, no RNG) must each be *refuted* from the specs alone; kill rate is the score, survivors are listed |
| R3 | **encode** | the fragment encoder accepts the module |
| R4 | **prove** | the prover verifies — proof additions allowed (executable `assert`s, `#@ proof` clauses, sidecar lemmas); **specs are frozen** |
| R5 | **fidelity** | the prover-compiled model agrees with CPython under Hypothesis |

Two properties fall out of this design that no static benchmark has:

1. **Spec quality is a measured dimension.** The grammar-contact exercise
   showed specs can pass every checker while being too weak (frame-cheats,
   threshold specs). R2 makes that mechanical: a weak spec survives mutants,
   and the survivor list says exactly which bug it cannot see.
2. **One corpus, many exams.** Because tasks are source modules, exam
   variants derive mechanically: strip the specs → a *spec-writing* task
   (score = rungs reached + kill rate of the written specs); strip the proof
   additions → a *proof-repair* task (score = R4 restored under the frozen
   specs); ship a surviving mutant → a *debugging* task. The golden corpus is
   the answer key for all of them. **The proof-repair exam is live**:
   `lemmapy benchmark --exam proof-repair [--engine claude|file:<dir>]`
   strips each sidecar-bearing task's `.proofs.dfy` (the `#@ proof` clauses
   stay in the frozen source) and scores restoration through the repair
   loop — the same whitelist and prover as the golden proof, so R4 must be
   re-earned, never asserted. Roster today: `gcd` (8-lemma divisibility
   pack) and `modp` (6-lemma mod/pow pack); executable proof-hint asserts
   are admitted source and stay.

## Backend policy (and the "ultimate benchmark" question)

Rungs R3–R5 are **backend-parameterized** — today they run against Dafny;
when a second backend lands (e.g. Lean), the same tasks get a second
prove/fidelity column. Same functions, same frozen specs, two provers: a
backend comparison only a multi-backend toolchain can make, and the payoff
for keeping the ladder backend-agnostic.

A cross-**tool** olympics (LemmaPy vs LemmaScript vs OpenJML vs Verus vs
Frama-C) is explicitly out of scope: it means building and maintaining
competitors' harnesses, cross-language ports make results incomparable, and
a benchmark authored by one competitor caps its own credibility — that is
VerifyThis/SV-COMP territory, which works because of neutral governance.
The portable middle path: task *contracts* are source-language-neutral, so
the corpus can be published as a spec suite others port to their tools.

## Task format

```
benchmark/tasks/<id>/
  task.py           # annotated Python — the single source of truth
  task.proofs.dfy   # optional ghost lemma sidecar (whitelist-validated)
  meta.json         # {id, origin, license} + adjudications:
                    #   equivalent_mutants[], timeout_kills[]
```

Seed corpus: 14 tasks (11 adapted from HumanEval, MIT; 3 project-original),
every one at full ladder height as the golden baseline. Growth is free:
each fragment slice makes more of the 20-task contact corpus (and the 65%
of HumanEval that surveys in-fragment) eligible — slice 6 (`sum()`/genexp
folds) admitted `below_zero` and `sum_squares`; slice 7 (`**` -> `PyPow`) admitted `modp` (whose mod/pow lemma sidecar joins the proof-repair exam roster) and, verified as-is, `triples_sum_to_zero`.

## Seed baseline (August 2026)

Full run (defaults: 8-mutant cap, 5s hunt budget, 60s prove budget,
60 fidelity examples per function):

```
task                   gate  hunt  mutants  encode  prove  fidelity  height
below_threshold        pass  pass  1/1      pass    pass   pass      6/6
below_zero             pass  pass  7/7      pass    pass   pass      6/6
bump                   pass  pass  2/2      pass    pass   pass      6/6
clamp                  pass  pass  2/2      pass    pass   pass      6/6
gcd                    pass  pass  2/2      pass    pass   pass      6/6
incr_list              pass  pass  2/2      pass    pass   pass      6/6
intersperse            pass  pass  3/3      pass    pass   pass      6/6
is_palindrome          pass  pass  4/4      pass    pass   pass      6/6
is_prime               pass  pass  7/7      pass    pass   pass      6/6
max_element            pass  pass  1/1      pass    pass   pass      6/6
modp                   pass  pass  6/6      pass    pass   pass      6/6
rolling_max            pass  pass  5/5      pass    pass   pass      6/6
sum_squares            pass  pass  6/6      pass    pass   pass      6/6
triples_sum_to_zero    pass  pass  8/8      pass    pass   pass      6/6

tasks: 14   full-ladder: 14   spec strength: 56/56 killed (+1 equivalent
adjudicated; modp's panel includes 1 adjudicated timeout kill — the
diverging `+` -> `-` loop mutant)
```

The benchmark's first run also exercised its adjudication path: the raw run
surfaced one surviving mutant on `max_element` (`>` → `>=` in the max
update) — a textbook *equivalent mutant* (identical output on every input;
it changes which of several equal elements is picked, unobservable in the
result). It is recorded in the task's `meta.json` under
`equivalent_mutants` and excluded from the panel, visibly counted in the
report. Survivors are guilty until adjudicated, never silently dropped.

A mutant whose hunt exhausts its wall is **inconclusive, not a kill**. It
is tempting to score it as killed — the common cause is a diverging loop
(e.g. `i += 1` → `i -= 1` in `modp`), and R4 proves termination — but R4
proves the *original* terminates, not the mutant, and a slow-but-
terminating analysis is indistinguishable from a diverging one at the
wall. Counting the timeout would let a merely-slow mutant publish a false
kill, a false full-ladder height, and a false aggregate score.

So timeouts follow the same discipline as survivors: **guilty until
adjudicated.** An unadjudicated timeout FAILS the rung, naming the mutant
and pointing at the remedy; a human who has confirmed the divergence
records it in the task's `meta.json` under `timeout_kills`, after which it
counts as a kill and is labeled distinctly in the rung detail (`k/N killed
(m adjudicated timeout kill(s))`). Mutants also run under a tighter wall
than the original so one diverging mutant cannot stall a panel, and a
launch failure remains an analysis ERROR that blocks the rung.

## Scoring and reproducibility

`lemmapy benchmark [--quick] [--report FILE]` prints the ladder table and
writes a JSON scorecard. Mutant panels are deterministic (ordered AST walk,
splice-based so `#@` comments survive verbatim). Surviving mutants may be
semantically equivalent rather than spec gaps — they are reported
individually for adjudication, standard mutation-testing practice. Tool
versions are pinned by the lockfile; the JSON report is append-only history
in spirit: regenerate, don't edit.
