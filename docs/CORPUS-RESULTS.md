# Fragment-Coverage Survey (August 2026)

> RQ1 data ([EVALUATION.md](EVALUATION.md)): the M0 read-only conformance survey (`veripy survey`) over nine typed OSS codebases, VeriPy itself, and the HumanEval/MBPP canonical solutions. **These numbers measure the survey prototype as much as the fragment** — read the method caveats before quoting them.

## Method

- Tool: `veripy survey` (AST-level rule pass, ~30 rules approximating the [ARCHITECTURE.md §3.1](ARCHITECTURE.md) checklist; see `veripy/frontend/conformance.py`).
- **No type information in the survey** (the basedpyright *type gate* is live for `veripy check` / `verify`; this survey pass does not use it): method calls are judged *optimistically by name* against the planned Tier 2 container/str surface; `Any` leaks, heterogeneous `==`, and subclass tricks are invisible. Survey acceptance is not encoder acceptance.
- Unit of measurement: the function (including methods). A function is *accepted* iff zero rules fire. Nested functions are scored independently and also fire `X-NESTED` on their parent.
- Package source directories only (no test suites). Corpus pinned by commit; survey at VeriPy `c9ca858`+survey branch.

## Results

| Corpus | Commit | Files | Functions | Accepted | LOC accepted |
| --- | --- | ---: | ---: | ---: | ---: |
| black (`src/black`) | 74371e2 | 25 | 452 | 103 (22.8%) | 12.0% |
| attrs (`src/attr`) | c1dc5dc | 13 | 214 | 32 (15.0%) | 10.7% |
| rich (`rich/`) | 9d8f9a3 | 100 | 912 | 53 (5.8%) | 3.9% |
| pydantic (`pydantic/`) | cc13d1b | 104 | 1871 | 103 (5.5%) | 3.1% |
| httpx (`httpx/`) | b5addb6 | 23 | 446 | 23 (5.2%) | 6.8% |
| returns (`returns/`) | 5efc2a5 | 115 | 655 | 21 (3.2%) | 1.9% |
| cattrs (`src/cattrs`) | f2e42f3 | 36 | 293 | 34 (11.6%) | 3.0% |
| structlog (`src/structlog`) | ab24a26 | 21 | 349 | 24 (6.9%) | 7.5% |
| typer (`typer/`) | dacef1b | 31 | 568 | 55 (9.7%) | 4.1% |
| veripy (`veripy/`) | — | 9 | 52 | 9 (17.3%) | 8.7% |

## The greenfield contrast: benchmark code

The same rules run over the canonical solutions of the two standard code-generation benchmarks (the LLM-greenfield thesis's home turf):

| Corpus | Tasks in-fragment |
| --- | ---: |
| HumanEval (164 canonical solutions) | **107 (65.2%)** |
| MBPP (974 canonical solutions) | **650 (66.7%)** |

Library plumbing sits at 3–23% coverage; benchmark-style algorithmic code sits at ~65%. This is the design's central bet made measurable: *the fragment is a generation target, not a filter on found code* — the kind of function LLMs are asked to write (and that specs naturally describe) is overwhelmingly fragment-shaped, while OO library internals are not and were never the v1 audience.

These figures are from the *post-review* rule engine: an adversarial review pass (19 confirmed findings, each reproduced against the live tool) closed several false-accept classes — aliased imports laundering `cast`/`importlib`, rebound `eval`, real `sys.modules` access shapes, true division `/`, expressions hiding in defaults and annotations, metaclasses — and fixed telemetry distortions (per-occurrence fire units, star-imports counted once per file, `# type: ignore` attributed to the innermost function only). Coverage numbers dropped 1–5 points versus the pre-review run, as expected when false-accepts close.

Top rules by fire count, pooled (full per-repo JSON in `build/survey-*.json`, regenerable):

| Rule | What it counts | Reading |
| --- | --- | --- |
| `U-METHOD` | method calls outside the modeled container/str surface | The dominant blocker everywhere — but the *most optimistic-biased* rule (name-only matching). Ranks Tier 2 surface growth. |
| `X-ATTR-STORE` | attribute assignment | OO mutation — the fragment's deliberate §5 exclusion showing up at scale |
| `X-CLASS-INHERIT` | methods of inheriting classes | Inheritance exclusion (v2 traits); dominant in rich |
| `T-FSTRING` | f-strings | Top *admittable* candidate — pure string interpolation is curated-model territory |
| `U-CALL` | calls to unmodeled names | Tier 3 extern-contract demand signal |
| `X-YIELD` / `X-RAISE` / `X-DECOR` | generators, raise, decorators | Matches the predicted v1.5 admission order in [ARCHITECTURE.md §7](ARCHITECTURE.md) |
| `F-DUNDER-ATTR` | `__dict__`/`__class__` access | attrs' metaprogramming core — correctly outside any shallow fragment |

## Interpretation (initial, one run)

1. **Brownfield coverage of idiomatic OO libraries is low (5–25% of functions), as the design predicted.** These corpora are the *hard* case: attrs is a metaprogramming library, rich is deeply OO. The greenfield thesis — the fragment as a *generation target* — is not contradicted by low found-code coverage; but these numbers set honest expectations for "point it at an existing repo."
2. **Function-level acceptance skews short** (accepted-LOC% ≈ half of accepted-functions% in black): small pure helpers pass; long orchestration functions fire something. Verified-island adoption will be helper-first.
3. **The admission priority signal is clear and stable across corpora:** f-strings, `raise`, generators-consumed-eagerly, and common decorators would each buy meaningful coverage; the Tier 2 method surface dominates everything.
4. **Caveat, repeated:** `U-METHOD`/`U-CALL` optimism means true coverage is *lower* than reported once types land; the exclusion-rule fires (`X-*`, `T-*`, `F-*`) are the reliable part.

## Next

- Wire the type gate into `veripy survey` so `U-*` rules are honest and `Any` leaks are visible
- Survey a stratified sample of strict-mode-clean packages beyond these nine
- Wire rule-fire telemetry into the v1.5 admission decision
