# lemmapy-benchmark

> **Status: v0 — runner and 12-task seed corpus shipped.** `lemmapy benchmark`
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
| R2 | **mutants** | **spec strength**: an auto-generated panel of single-fault mutants (operator swaps, off-by-ones — deterministic, no RNG) must each be *refuted* from the specs alone; the refutation rate is the score, survivors are listed. A mutant that makes the code **crash** (IndexError, ZeroDivisionError, …) is reported separately and **never credited**: the interpreter caught it, not the specification, and `#@ ensures True` catches it just as well |
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
   re-earned, never asserted. Roster today (5 tasks, each with a
   sidecar-less control pinned by `test_sidecar_is_load_bearing`): `gcd`
   (8-lemma divisibility pack), `is_prime` (7-lemma sqrt-bounded
   primality pack sharing gcd's lemma family), `below_zero` (`SliceSnoc`),
   `rolling_max` (`SeqMaxDominates` induction), `sum_squares`
   (`SumNonNeg`, instantiated at a mapped-seq `#@ proof` argument).
   Executable proof-hint asserts remain admitted source and stay where
   present. The divisibility family is deliberately NOT promoted into the
   preamble while the exam depends on those lemmas being absent.

   **The spec-writing exam is live too**: `lemmapy benchmark --exam
   spec-writing` strips every `#@` line, hands the engine the bare
   implementation, and scores the specification it writes back on the same
   deterministic panel as the golden — engine kill rate beside golden kill
   rate. Its correctness rests on four properties, each pinned by tests:

   - **Source freeze.** Dropping full-line `#@` comments from the answer
     must reproduce the stripped input *exactly*. Text equality is
     authoritative, not AST equality: an inserted blank line is
     AST-invisible, and an engine free to edit the implementation can
     always weaken the task to fit a trivial spec.
   - **No verification feedback.** Retries fire only for mechanical
     invalidity (unparseable, freeze violation, malformed clause, no
     postcondition at all). Feeding prover outcomes back would silently
     turn this into the proof-repair exam.
   - **Fair baseline.** The golden is scored under identical exam
     conditions — its own `#@ proof` clauses stripped and no sidecar
     staged — so the engine is never compared against a run that had
     lemmas available. (`#@ proof` clauses are rejected in this exam;
     there is no sidecar channel for them to name.)
   - **Panel alignment.** Mutations sort by `(line, col, replacement)` and
     inserting `#@` lines is a monotone renumbering, so ordering survives
     and the `max_mutants` truncation selects the same faults; line-numbered
     `equivalent_mutants` are translated through the same map. Untranslated,
     the adjudication would silently miss and the engine would be charged
     for a mutant the golden run was forgiven.

   The anti-gaming property is the design's whole point, and it is
   measured, not asserted. An adversarial arm replaces every task's
   specification with `#@ ensures True` (keeping only the golden
   `#@ requires`, so the inputs are the same) and runs the whole corpus:

   ```
   arm                    refuted    crashed   valid
   tautology (ensures True)  0/39 (0%)     15    12/12
   golden                   26/39 (67%)    13      —
   ```

   All twelve tautologies clear the type gate, the runtime-contract hunt,
   the encoder, and the SMT prover — *every automated check the toolchain
   has* — and the panel scores them at zero.

   **This measurement is the reason R2 separates refutations from
   crashes.** Before the split, a tautology scored **38%**, because
   CrossHair exits non-zero on an uncaught `IndexError` just as it does on
   a violated postcondition, and the harness credited both. The metric's
   zero point was 38%, and on `max_element` and `gcd` a tautology was
   *indistinguishable from golden*. Counting only refutations moves the
   floor to a true 0% — and honestly lowers the golden baseline from a
   flattering 39/39 to **26/39**, because 13 of golden's own kills were
   crashes too. A narrower claim, but a real one, and the dynamic range it
   opens (0% → 67%) is what lets the rung rank anything at all.

   `max_element` is now visibly the corpus's weakest specification (0/1):
   its single mutant is caught only by a crash. That is exactly the kind of
   gap the rung exists to surface, and it was invisible while crashes
   counted.

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
  meta.json         # {id, origin, license}
```

Seed corpus: 12 tasks (9 adapted from HumanEval, MIT; 3 project-original),
every one at full ladder height as the golden baseline. Growth is free:
each fragment slice makes more of the 20-task contact corpus (and the 65%
of HumanEval that surveys in-fragment) eligible — slice 6 (`sum()`/genexp
folds) admitted `below_zero` and `sum_squares`.

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
rolling_max            pass  pass  5/5      pass    pass   pass      6/6
sum_squares            pass  pass  6/6      pass    pass   pass      6/6

tasks: 12   full-ladder: 12   spec strength: 26/39 mutants REFUTED by the specs (67%); 13 crashed (caught by the interpreter, not the spec — never credited)
```

The benchmark's first run also exercised its adjudication path: the raw run
surfaced one surviving mutant on `max_element` (`>` → `>=` in the max
update) — a textbook *equivalent mutant* (identical output on every input;
it changes which of several equal elements is picked, unobservable in the
result). It is recorded in the task's `meta.json` under
`equivalent_mutants` and excluded from the panel, visibly counted in the
report. Survivors are guilty until adjudicated, never silently dropped.

## Scoring and reproducibility

`lemmapy benchmark [--quick] [--report FILE]` prints the ladder table and
writes a JSON scorecard. Mutant panels are deterministic (ordered AST walk,
splice-based so `#@` comments survive verbatim). Surviving mutants may be
semantically equivalent rather than spec gaps — they are reported
individually for adjudication, standard mutation-testing practice. Tool
versions are pinned by the lockfile; the JSON report is append-only history
in spirit: regenerate, don't edit.
