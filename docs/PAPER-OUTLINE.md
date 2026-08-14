# Paper outline — VeriCodeGen @ NeurIPS 2026

> **Target.** 4–8 pages excluding references, non-archival, **double-blind**,
> OpenReview. Abstract **Sept 11**, paper **Sept 13** (AoE). Template:
> `neurips_2026_vericode_workshop.tex` (style modifications are desk-reject).
>
> **Status.** Skeleton with slots for every number. A slot marked ⬛ has a
> measured value in the repo; ⬜ is still to run. Every ⬛ must carry the
> exact command that regenerates it (existing EVALUATION.md discipline).

## Framing

A **benchmark/methodology** paper, not a system paper. The system is
substrate (~1.5pp); the contribution is *what gets measured and how the
measurement is kept honest*.

Working title: *Measuring Specification Strength, Not Just Proof Success.*

### The three claims

1. **Spec strength is mechanically measurable.** A deterministic mutant
   panel scores whether a specification is worth proving. Proof-completion
   benchmarks score one verified/failed bit and cannot see this.
2. **One golden corpus yields many exams.** Proof-repair and spec-writing
   exams derive mechanically from the same annotated modules, scored by the
   same prover and the same whitelist.
3. **Agentic verification benchmarks leak, and the leaks are measurable.**
   A contamination-hardened protocol, plus the harness defects that
   produced both a false-perfect and a false-zero before any real number
   existed.

## Section plan

### 1. Introduction (~0.75pp)
The hook is the measured anti-gaming result, stated early:

> ⬛ Replace every specification in the corpus with `#@ ensures True`. All
> twelve tautologies clear the type gate, the runtime-contract hunt, the
> encoder, and the SMT prover — every automated check the toolchain has.
> The mutant panel scores them **0/39**, against **26/39** for the
> hand-written specifications (both on the pre-operand panel; the current
> panel puts golden at 34/47).

That is the paper in one experiment: *passing a verifier says nothing about
whether the property proved was worth proving.*

**And the second-order result is the methodological one.** Getting that
number right required separating two things the obvious implementation
conflates. CrossHair exits non-zero both when a postcondition is violated
and when the mutant simply *crashes*, and crediting both gave the tautology
**38%** — with `max_element` and `gcd` scoring *identically to golden*. The
metric's zero point was 38%, and nobody reading "kill rate" would know.
Counting only refutations moves the floor to a true 0% and honestly lowers
the golden baseline from a flattering 39/39 to 26/39, because 13 of
golden's own kills were crashes. Narrower claim, real dynamic range.

Worth stating plainly in the paper: this class of error is invisible to
every check except an adversarial arm that *should* score zero. Any
mutation-based spec-quality metric that does not report its trivial-spec
floor is not interpretable, and we did not find one that does.

### 2. Substrate (~1.5pp)
Annotated production Python (`#@` comments) → typed fragment → Dafny.
Four soundness layers, compressed. The **sidecar whitelist** gets real
space because it is load-bearing for the exams: proof additions are
whitelist-validated ghost declarations with bodies, so a repair can never
smuggle an axiom. Table: threat → mechanism (from ARCHITECTURE.md).

### 3. The assurance ladder and the mutant panel (~1.5pp)
R0–R5. Why R2 is the novel rung. Determinism argument (ordered AST walk,
no RNG) and why determinism is what makes cross-condition comparison legal.
Adjudication protocol for equivalent mutants (raw *and* adjudicated rates
reported).

⬛ Golden baseline: 12 tasks, 12/12 full ladder, **34/47 mutants refuted
(72%)**, 13 crashed and not credited. `lemmapy benchmark`

### 4. Derived exams (~1.5pp)
- **Proof-repair**: strip `.proofs.dfy`, restore R4 under frozen specs.
  Roster ⬛ n=5, each with a **pinned load-bearing control** (the
  sidecar-less variant must fail, else the row measures nothing).
- **Spec-writing**: strip every `#@` line, score the specification written
  back on the *identical* panel. Four correctness properties, each pinned
  by tests: source freeze (text-authoritative, since blank-line insertion
  is AST-invisible), no verification feedback in retries, fair baseline
  (golden scored under identical no-sidecar conditions), panel alignment.

Include the **panel-alignment argument** explicitly — it is the load-bearing
lemma of the whole comparison: mutations sort by `(line, col, replacement)`
and inserting comment lines is a monotone renumbering, so ordering survives
and the `max_mutants` truncation selects the same faults.

State one consequence plainly, before a reviewer reads it as a flaw: on the
five sidecar-bearing tasks the spec-writing exam has a **ladder ceiling
below R4**, because the proof channel is deliberately closed (no sidecar,
`#@ proof` rejected) and those tasks provably cannot prove without lemmas.
Both sides face that ceiling — the golden baseline is scored under the same
conditions — so heights are reported relative to the golden's
exam-conditions height, and R2 kill rate, which is unaffected by the proof
channel, remains the headline.

### 5. Experimental protocol (~1pp) — the contamination section
The section reviewers will remember. Everything here is already recorded.

- ⬛ **Answer-key retrieval.** A tool-enabled headless agent found the
  golden sidecar in the repository and returned it verbatim
  (comment-for-comment identical; caught because all eight helper-lemma
  names matched, which independent derivation would not produce). A
  perfect score measuring retrieval.
- ⬛ **The false zero.** The first hardening attempt placed the prompt
  after `--disallowedTools`, a variadic flag that swallowed it as
  tool-name rules; every iteration errored, scoring 0/1 for reasons
  unrelated to proofs.
- ⬛ **Probe discipline.** Tool denial verified by a live probe with an
  unguessable token file — a first probe against `/etc/hosts` was itself
  invalid, since the model can recite that file from world knowledge.
- ⬛ **Eight harness defects, each of which would have silently corrupted a
  headline number.** None was caught by the test suite; each was found by
  a live smoke run or an adversarial arm. This table is the section.

  | # | Defect | Silent effect on the number |
  |---|---|---|
  | 1 | Kill rate credited **crashes** as refutations (CrossHair exits non-zero for both) | Tautology floor was **38%, not 0%**; on two tasks a tautology was *indistinguishable from golden* |
  | 2 | A spec refuted at R1 short-circuits before the panel, contributing 0/0 | Writing a **false** spec outscored writing a weak one — failure was profitable |
  | 3 | Dafny's warnings-as-errors overrode "N verified, 0 errors" | `failed` with **zero** failure records — a payload no repair loop can act on |
  | 4 | Whitelist rejected `decreases \|s\|` before a body brace | Every engine writing idiomatic Dafny burned an iteration on a spurious rejection |
  | 5 | Equivalent-mutant map composed in the wrong coordinate system | Exclusion missed; engine strength biased **downward** on every adjudicated task |
  | 6 | Mutant identity keyed by line only, not (line, column) | One adjudication could silently retire **two** distinct faults |
  | 7 | Panel had no **operand**-replacement family, only operator families | A spec that never says which input the result depends on scored 100%; `clamp`'s golden spec — satisfied by `return lo` — was indistinguishable from one that determines the function |
  | 8 | The `max_mutants` cap truncated by position | The panel became a *line-prefix* of the function; `is_prime` hit the cap exactly, so its back half went unprobed |

  Defects 1 and 2 are the interesting ones, because they are *scoring*
  bugs rather than plumbing bugs: the harness ran, produced plausible
  numbers, and those numbers were wrong in a direction that flattered the
  system. Both were found by an adversarial arm that *should* score zero —
  which is the generalizable recommendation.

  **Three protocol rules we would give anyone building one of these:**
  1. *Run a trivial-spec arm and publish its score.* A metric whose floor
     is unmeasured is uninterpretable; ours was 38% and looked fine.
  2. *Make the denominator independent of the system under test.* Anything
     that lets a subject drop a task from its own denominator rewards
     failing.
  3. *Validate with positive AND negative probes.* A good score and a bad
     score are equally suspect until the harness is instrumented — we
     produced one false-perfect (answer-key retrieval) and one false-zero
     (a swallowed prompt) before either real number existed.

### 6. Results (~2pp)
| Table | Content | Status |
|---|---|---|
| T1 | Proof-repair: arms (full / one-shot / ablated) × engines, restored k/n with Wilson CIs | ⬜ needs matrix run |
| T2 | Iterations-to-restore and token/cost per engine | ⬜ |
| T3 | Whitelist rejections by rule — proposals that attempted axioms | ⬜ |
| T4 | Spec-writing: engine kill rate vs golden on the identical panel, per task | ◐ 4-task pilot done; 12-task run in flight |
| T5 | Engine-pack structural divergence from golden | ⬛ seed: gcd, 8 lemmas under a different decomposition (`DivModRel`, `MulMono`, …; 130 lines vs golden 115), sharing only the entry point the frozen `#@ proof` clause names |

**⚠ The prediction this section was written to confirm is FALSIFIED, and
the paper must lead with that.**

First full run (12 tasks, `claude:sonnet`, one trial): **11/12 valid, and
every valid answer scored 100% kill rate — exactly matching golden.** The
predicted "engine specs score below golden" separation did not appear.

Diagnosis, and it is not "the model is good":

⬛ **The panels are too small to rank anything.** Median panel is **2.5
mutants**; **6 of 12 tasks have ≤2**; `below_threshold` has **exactly
one**. A kill rate computed over one mutant carries one bit. The metric
cannot resolve differences between strong specifications because there is
almost nothing to resolve them with.

```
panel size:  1 1 2 2 2 2 2 3 3 4 5 6 8      (n=12, total 40, median 2.5)
operators:   `+`->`-` (8), `1`->`2` (8), `0`->`1` (6), `-`->`+` (3),
             `==`->`!=` (3), `<`->`<=` (2)
```

**The honest claim, revised.** Mutant kill rate is a *sound but
low-resolution* instrument: high precision at the bottom of the range —
it decisively catches specifications that every other checker in the
toolchain accepts (⬛ 0/3 on both vacuous and tautological specs) — and
**no resolution at the top** on this corpus. Ranking strong specifications
against each other needs materially larger panels.

This reframes the contribution rather than sinking it, and the CFP
explicitly invites negative results. It also yields the concrete next
experiment (WS6): extend the operator set beyond the current five classes
and re-baseline. Report the before/after panel sizes — the fact that
resolution is a *function of operator design*, and that most spec-quality
work never states its panel size, is itself a finding worth publishing.

**Also observed:** spec **strength** and **provability** separate — an
engine spec matching golden's kill rate still failed to prove, reaching a
lower ladder height. Different axes; a benchmark reporting only "verified"
conflates them.

**Grammar-ergonomics confound, found and fixed.** The single invalid
answer (`is_prime`) was not a weak specification: the engine wrote the
correct two-way implication form and was rejected because a quantifier
used as an operand of `and`/`or` must be parenthesized — a rule the
instructions never stated. The exam was partly measuring "did you guess
the syntax convention." Rules updated (`spec-rules/2`) and versioned into
every ledger row, since kill rates are only comparable across engines that
saw the same instructions. Worth a sentence in the paper: a spec-writing
exam doubles as a grammar-ergonomics probe, and this is what it found.

### 7. Limitations (~0.5pp) — written before reviewers write them
- Roster n=5 for proof-repair; 12-task corpus. Methodology + seed corpus,
  not a large-scale benchmark.
- Difficulty ceiling: no dict/set, no indexed assignment, so no DP tasks.
  State it; do not let a reviewer find it.
- 9/12 tasks HumanEval-derived. The sandbox stops *retrieval*; it cannot
  stop **memorization**. What is measured is construction against a frozen
  spec and whitelist — and the golden packs for the four newest roster
  tasks are unpublished until camera-ready.
- Mutation-testing's known limits applied to specs: operator-selection
  bias, equivalent mutants. Kill rate on single-fault operator swaps is a
  *lower bound* on spec weakness, not a full measure of strength.
- Fragment coverage is honest but caveated: ⬛ 3–23% of functions in nine
  OSS libraries vs ⬛ ~65% of HumanEval/MBPP — and the survey is
  optimism-biased (no type information yet), so true coverage is lower.

### 8. Related work
DafnyBench, MBPP-DFY, Clover, dafny-annotator; Nagini, Verus,
Strata-Python; CrossHair/icontract. **Action item:** the red-team was
asked to surface prior work on *mutation-testing specifications* — an
uncited near-neighbour there is the biggest desk-reject risk in the paper.

## Anonymization checklist (double-blind)
- [ ] Neutral tool name throughout; no repo URL
- [ ] Anonymized artifact (anonymous.4open.science)
- [ ] Self-citations in third person
- [ ] No acknowledgements
- [ ] New golden sidecars stay off public branches until camera-ready

## Open risks
1. ⬜ No `OPENAI_API_KEY` / `OPENROUTER_API_KEY` in the environment — the
   GPT-family and open-model columns cannot run. Claude-family via CLI
   works today. **Needs the user.**
2. ⬜ Matrix wall-clock: resume + per-row ledger flush make it
   interruptible, but the full grid is hours.
3. ⬜ CrossHair timeout flakiness could bias kill rates if engine specs are
   systematically more expensive than golden — check before reporting.
