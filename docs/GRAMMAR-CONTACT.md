# Grammar-Contact Exercise (August 2026)

> The M0 exit test for the `#@` spec surface: 20 functions from HumanEval/MBPP — selected as in-fragment by `veripy survey`, adapted minimally, annotated with real contracts — pushed through `veripy check` (grammar + strict type gate) → `veripy hunt` (CrossHair must find nothing) → mutation testing (CrossHair must refute a seeded bug), then independently reproduced and adversarially re-mutated by separate verifiers. The corpus lives in [`examples/contact/`](../examples/contact/); every grammar friction was logged as a first-class deliverable.

## Results

- **20/20 tasks verified-clean**: specs written in grammar v0, accepted by the parser and the strict type gate, no CrossHair counterexamples against the canonical algorithms.
- **20/20 writer mutants caught**: every seeded bug (off-by-ones, wrong comparisons, dropped cases) produced a CrossHair counterexample from the specs alone.
- **20/20 independently reproduced** by adversarial verifiers.
- **Spec strength: 15 strong, 5 partial** — verifiers wrote their own mutants *designed to slip past the stated ensures*; five did, in two distinct and instructive ways (below).
- **26 frictions logged**, clustering into seven findings.

## The two spec-gap classes the adversarial pass found

**1. Post-state ensures admit frame-cheats (3 tasks: he_5, mbpp_97, he_35).** Ensures written over a mutable parameter's *post-state* (`forall i in range(len(l)) :: ...`) are satisfied by an implementation that mutates the input and returns values consistent with the mutation (`l[:] = [0]; return 0` passes check *and* hunt). This is not primarily a grammar gap — `old()` exists and one token fixes each case — it is a **system finding**: the post-state idiom is sound in the M1 target, where the ownership discipline ([ARCHITECTURE.md §3.2](ARCHITECTURE.md)) rejects parameter mutation outright and guards copy-in ([§4.1](ARCHITECTURE.md)), but in M0's runtime-only mode nothing yet enforces parameter purity. Until the conformance checker lands: **runtime-first specs over mutable parameters should use `old(param)`**. That dynamic checking alone cannot defend against input mutation without snapshots is precisely the §4.1 copy-in rationale, observed in the wild.

**2. Optimality contracts over subsequences are inexpressible with bounded executable quantifiers (2 tasks: mbpp_149, mbpp_247).** "Longest subsequence such that…" needs quantification over all subsequences; the executable workaround (boundary characterizations: exact iffs at the extremes, bounds between) leaves the middle of the range unpinned, and verifiers built threshold-satisfying wrong implementations proving it. Subset quantification over *small index sets* is expressible (mbpp_620 encodes subsets as bitmasks, `exists mask in range(2**n)` — an O(2ⁿ·n²) executable spec that CrossHair handles). This is a real, documented expressiveness boundary of the runtime-executable spec fragment; witness-plus-maximality machinery is proof-backend territory.

## Friction findings → decisions

| # | Finding (tasks) | Decision |
| - | --- | --- |
| 1 | **No `<==>`** — iff written as `(A) == (B)`, where forgetting parentheses silently becomes a chained comparison (5 tasks) | **Fixed now**: `<==>` added to the grammar (v0.1), loosest precedence, desugars to `bool(A) == bool(B)` |
| 2 | **Reserved `result` collides with idiomatic local names** — canonical code routinely names its accumulator `result` (4 tasks renamed locals) | Keep reserved (the ensures meaning wins); document the rename convention; better diagnostic when the collision fires |
| 3 | **For-each loops have no nameable iteration state** for invariants — writers rewrote `for e in l` into indexed/while loops so an invariant could quantify over the processed prefix (5 tasks) | v1 spec-language design item: ghost variables / spec-visible loop index. Related: basedpyright flags variables used *only* in specs (`enumerate` index) as unused — conformance-integration item |
| 4 | **No named spec helpers** — a ~120-char subformula duplicated across two ensures; a binomial reference function needed for `ncr_modp` (2 tasks) | v1 candidate: `#@ define`; interim: module-level reference functions (they are Tier-3-shaped trusted helpers and must be treated as such) |
| 5 | **`old()` not allowed in invariants** — Euclid's invariant wants entry values of mutated variables (1 task) | Deferred with a clean workaround (run the algorithm on fresh locals); revisit with the ghost-variable design |
| 6 | **Unbounded maximality quantifiers** (`forall d :: d > result ==> ...`) — bounded manually with a justification comment (1 task) | Known v0 decision (bounded domains are what makes M0 executable); guard-form unbounded quantifiers remain a proof-backend candidate |
| 7 | **Invariants are recorded, not enforced** — mutation testing exercises only requires/ensures (noted by one batch) | By design in M0 (invariants are Dafny-backend inputs); worth a runtime invariant-checking mode later if M0 lives long |

## Grammar verdict

**Frozen as v0.1** = v0 + `<==>`. Nothing in twenty real tasks required a redesign: every value-level functional contract was expressible (two optimality contracts hit the documented executable-fragment boundary, not a grammar defect), quantifiers with dependent domains (`j in range(i+1, len(l))`) compose correctly, and the desugaring survived adversarial use. The deferred list (ghosts, `#@ define`, `old()` in invariants, unbounded quantifiers) is v1 spec-language work, tracked here and in [SPEC-GRAMMAR.md](SPEC-GRAMMAR.md).

## M0 exit assessment

All three exit criteria are now met:

1. *Specs execute as runtime contracts on real code with counterexamples produced* — 20 independent tasks, 40 mutants hunted, 35 refuted by CrossHair from specs alone (the 5 survivors being the documented gap classes above).
2. *Fragment-coverage numbers for a handful of typed OSS repos* — nine repos plus the HumanEval/MBPP greenfield contrast ([CORPUS-RESULTS.md](CORPUS-RESULTS.md)).
3. *Grammar survived contact without redesign* — one additive change (`<==>`), zero breaking changes.
