# lemmapy-benchmark

> **Status: v0 — runner and 16-task golden corpus shipped.** `lemmapy benchmark`
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
   re-earned, never asserted. Roster today (7 tasks, each with a
   sidecar-less control pinned by `test_sidecar_is_load_bearing`): `gcd`
   (8-lemma divisibility pack), `modp` (6-lemma mod/pow pack), `is_prime`
   (7-lemma sqrt-bounded primality pack sharing gcd's lemma family),
   `below_zero` (`SliceSnoc`), `rolling_max` (`SeqMaxDominates`
   induction), `sum_squares` (`SumNonNeg`, instantiated at a mapped-seq
   `#@ proof` argument), `sum_to_n` (`GaussStep` over
   `ConsecutiveEven`, the parity fact the two floor divisions hide).
   This list is the enforced one: `test_roster_matches_the_docs` fails
   if it drifts from the roster the exam actually runs.
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
     and the `max_mutants` truncation selects the same faults; both
     line-numbered adjudication channels — `equivalent_mutants` and
     `timeout_kills` — are translated through the same map. Untranslated,
     an adjudication silently misses: the exclusion is lost and the engine
     is charged for a mutant the golden run was forgiven, or (for
     `timeout_kills`, which the runner validates against the panel) the
     ruling matches nothing and the whole panel errors as stale.

   **The timeout-bias check.** A refutation gap between the arms is a
   *strength* gap only if both arms concluded on the same mutants. A hunt
   that exhausts its wall is inconclusive, and engine-written specs can be
   systematically more expensive to hunt than golden ones — more
   quantifiers, wider domains — without being any weaker. Counting those
   as "not refuted" would report hunt COST as spec strength.

   So every row records WHICH mutants went inconclusive in each arm, in the
   stripped source's line numbering — the one coordinate system the two
   arms share. Identities, not counts: one arm exhausting its wall on
   mutant A while the other exhausts it on mutant B leaves each arm missing
   a different mutant, and equal counts would have called that comparable.
   A row whose arms disagree is marked `!` and named in a `TIMEOUT BIAS`
   line saying the gap must not be quoted as a strength difference, and it
   is **excluded from the aggregate** — quoting it in the headline would be
   the same defect one level up, where the `!` no longer travels with the
   number. The headline says how many rows it covers; if no row is
   comparable it states `NOT AGGREGATED` rather than an average of nothing.
   When the arms agree, the report says `timeout-bias check: PASSED`
   explicitly, so a reader never has to assume the check was done. The
   check is symmetric — golden timing out more disqualifies the comparison
   just as loudly, since that direction flatters the engine.

   The golden baseline is cached, and the cache key carries a schema
   version for the same reason: an entry written before a field existed
   matches an unchanged key, so "we never recorded golden's timeouts" would
   load as "golden never timed out" — a PASSED verdict drawn from data
   nobody collected.

   The anti-gaming property is the design's whole point, and it is
   measured, not asserted. An adversarial arm replaces every task's
   specification with `#@ ensures True` (keeping only the golden
   `#@ requires`, so the inputs are the same) and runs the whole corpus:

   ```
   arm                    refuted    crashed   valid
   tautology (ensures True)  0/39 (0%)     15    12/12
   golden                   26/39 (67%)    13      —
   ```

   *(Both figures predate the operand-replacement family and the modp/
   triples tasks; the golden baseline on the current 16-task panel is
   62/77 = 81%.)*

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

### Operator families, and why operand replacement had to exist

The panel's original five families all perturb an **operator** (comparison
swaps, `+`/`-`, integer ±1, `min`/`max`, `and`/`or`). None perturbs an
**operand** — so a specification that never says *which input the result
depends on* scored full marks.

`clamp` was the corpus's own counterexample. Its spec used to read
`ensures result == x or result == lo or result == hi`, which is satisfied
by `return lo` — a clamp that ignores its input entirely. On the old panel
that spec scored **2/2 (100%)**, indistinguishable from one that determines
the function.

Adding **operand replacement** (swap a parameter read for another
parameter of the *same declared type* — always in scope and type-compatible,
so the mutant is a genuine wrong-variable bug rather than a `NameError` or
`TypeError` the interpreter would catch) separates them:

```
clamp spec                                    refuted
"result is one of x, lo, hi"  (old golden)     4/8  (50%)
case-split spec that DETERMINES the function   8/8  (100%)
```

The corpus's own `clamp` spec was strengthened as a result — a golden task
is supposed to be the answer key. Panel totals went 40 → 47 mutants, median
2.5 → 3.5 per task, and the cap rose to 12.

**The cap is applied round-robin across families, not by position.** A
positional cap makes the panel a *line-prefix* of the function: `is_prime`
hit the old cap exactly, so its panel silently became "the first 8 sites in
line order" and the back half of the function went unprobed.

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

Seed corpus: 16 tasks (12 adapted from HumanEval, MIT; 4 project-original),
every one at full ladder height as the golden baseline. Growth is free:
each fragment slice makes more of the 20-task contact corpus (and the 65%
of HumanEval that surveys in-fragment) eligible — slice 6 (`sum()`/genexp
folds) admitted `below_zero` and `sum_squares`; slice 7 (`**` -> `PyPow`) admitted `modp` (whose mod/pow lemma sidecar joins the proof-repair exam roster) and, verified as-is, `triples_sum_to_zero`.

## Seed baseline (August 2026)

Full run (defaults: 12-mutant cap, 5s hunt budget, 60s prove budget,
60 fidelity examples per function):

```
task                   gate     hunt     mutants  encode   prove    fidelity height
below_threshold        pass     pass     1/1?     pass     pass     pass     6/6
below_zero             pass     pass     3/3      pass     pass     pass     6/6
bump                   pass     pass     2/2?     pass     pass     pass     6/6
clamp                  pass     pass     8/8      pass     pass     pass     6/6
gcd                    pass     pass     4/4      pass     pass     pass     6/6
incr_list              pass     pass     2/2?     pass     pass     pass     6/6
intersperse            pass     pass     1/3      pass     pass     pass     6/6
is_palindrome          pass     pass     2/4      pass     pass     pass     6/6
is_prime               pass     pass     8/8      pass     pass     pass     6/6
isqrt                  pass     pass     8/8      pass     pass     pass     6/6
max_element            pass     pass     0/1*?    pass     pass     pass     6/6
modp                   pass     pass     7/8*     pass     pass     pass     6/6
rolling_max            pass     pass     1/5      pass     pass     pass     6/6
sum_squares            pass     pass     2/6      pass     pass     pass     6/6
sum_to_n               pass     pass     5/6*     pass     pass     pass     6/6
triples_sum_to_zero    pass     pass     8/8      pass     pass     pass     6/6
-----------------------------------------------------------------------------------
tasks: 16   full-ladder: 16   spec strength: 62/77 mutants REFUTED by the specs (81%); 13 crashed (caught by the interpreter, not the spec — never credited); 2 diverged (adjudicated nontermination — caught by the wall, not the spec, so never credited)
panel resolution: median 4.5 mutants/task, min 1, max 8; 4 task(s) marked ? — panel too small for a per-task rate to be comparable
* 2 mutant(s) human-adjudicated as divergent; counted separately, NOT as spec strength; 1 mutant(s) excluded as adjudicated equivalent
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

### Adjudications are identified, validated, and never laundered

Both channels key on the mutant's **description**, which names the exact
site (`line 27 col 14: `+` -> `-``). The column is load-bearing: without
it two mutations on one line share a description, and a single human
ruling would silently apply to both — an adversarial review demonstrated
a ruling about a genuinely *equivalent* mutant erasing a genuinely
*behavior-changing* one from the denominator and republishing the panel
as 100% spec strength.

Every adjudication entry must therefore match **exactly one** mutant in
the generated panel. An entry matching zero (a typo, or a stale ruling
after a source edit shifted the site) or several makes the panel's
meaning unknown, so the rung ERRORs and names the offending entry rather
than scoring. A panel whose every mutant was ruled equivalent measured
nothing and FAILs — it must not read as a skipped-because-absent rung,
which would count toward ladder height.

Finally, the scorecard never passes human judgement off as measurement:
a panel containing adjudicated kills or exclusions is starred (`6/6*`)
and footnoted with the exact counts, so `6/6*` is visibly not the same
claim as `6/6`.

## Scoring and reproducibility

A note on determinism: mutant *generation* is deterministic (ordered AST
walk, splice-based), but the *hunter* is a subprocess and can fail
intermittently — one run in five on an otherwise-clean commit exited 2
with an analysis error that a repeat run did not reproduce. That is the
ERROR path behaving correctly (an unmeasured mutant must not be scored),
so the rung names the offending mutant *and the hunter's reason*, making
an intermittent failure diagnosable rather than an unactionable
"1 analysis error(s)".

`lemmapy benchmark [--quick] [--report FILE]` prints the ladder table and
writes a JSON scorecard. Mutant panels are deterministic (ordered AST walk,
splice-based so `#@` comments survive verbatim). Surviving mutants may be
semantically equivalent rather than spec gaps — they are reported
individually for adjudication, standard mutation-testing practice. Tool
versions are pinned by the lockfile; the JSON report is append-only history
in spirit: regenerate, don't edit.
