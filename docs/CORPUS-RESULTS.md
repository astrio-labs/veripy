# Fragment-Coverage Survey — Initial Run (August 2026)

> First RQ1 data point ([EVALUATION.md](EVALUATION.md)): the M0 read-only conformance survey (`lemmapy survey`) run over three typed OSS codebases and LemmaPy itself. **These numbers measure the survey prototype as much as the fragment** — read the method caveats before quoting them.

## Method

- Tool: `lemmapy survey` (AST-level rule pass, ~30 rules approximating the [ARCHITECTURE.md §3.1](ARCHITECTURE.md) checklist; see `lemmapy/frontend/conformance.py`).
- **No type information yet** (basedpyright integration pending): method calls are judged *optimistically by name* against the planned Tier 2 container/str surface; `Any` leaks, heterogeneous `==`, and subclass tricks are invisible.
- Unit of measurement: the function (including methods). A function is *accepted* iff zero rules fire. Nested functions are scored independently and also fire `X-NESTED` on their parent.
- Package source directories only (no test suites). Corpus pinned by commit; survey at LemmaPy `c9ca858`+survey branch.

## Results

| Corpus | Commit | Files | Functions | Accepted | LOC accepted |
| --- | --- | ---: | ---: | ---: | ---: |
| black (`src/black`) | 74371e2 | 25 | 452 | 103 (22.8%) | 12.0% |
| attrs (`src/attr`) | c1dc5dc | 13 | 214 | 32 (15.0%) | 10.7% |
| rich (`rich/`) | 9d8f9a3 | 100 | 912 | 53 (5.8%) | 3.9% |
| lemmapy (`lemmapy/`) | — | 9 | 52 | 9 (17.3%) | 8.7% |

These figures are from the *post-review* rule engine: an adversarial review pass (19 confirmed findings, each reproduced against the live tool) closed several false-accept classes — aliased imports laundering `cast`/`importlib`, rebound `eval`, real `sys.modules` access shapes, true division `/`, expressions hiding in defaults and annotations, metaclasses — and fixed telemetry distortions (per-occurrence fire units, star-imports counted once per file, `# type: ignore` attributed to the innermost function only). Coverage numbers dropped 1–5 points versus the pre-review run, as expected when false-accepts close.

Top rules by fire count, pooled (full per-repo JSON in `build/survey-*.json`, regenerable):

| Rule | What it counts | Reading |
| --- | --- | --- |
| `U-METHOD` | method calls outside the modeled container/str surface | The dominant blocker everywhere — but the *most optimistic-biased* rule (name-only matching). Ranks Tier 2 surface growth. |
| `X-ATTR-STORE` | attribute assignment | OO mutation — the fragment's deliberate §5 exclusion showing up at scale |
| `X-CLASS-INHERIT` | methods of inheriting classes | Inheritance exclusion (v2 traits); dominant in rich |
| `T-FSTRING` | f-strings | Top *admittable* candidate — pure string interpolation is curated-model territory |
| `U-CALL` | calls to unmodeled names | Tier 3 extern-contract demand signal |
| `X-YIELD` / `X-RAISE` / `X-DECOR` | generators, raise, decorators | Matches the predicted v1.5 admission order in [ROADMAP.md](ROADMAP.md) |
| `F-DUNDER-ATTR` | `__dict__`/`__class__` access | attrs' metaprogramming core — correctly outside any shallow fragment |

## Interpretation (initial, one run)

1. **Brownfield coverage of idiomatic OO libraries is low (5–25% of functions), as the design predicted.** These corpora are the *hard* case: attrs is a metaprogramming library, rich is deeply OO. The greenfield thesis — the fragment as a *generation target* — is not contradicted by low found-code coverage; but these numbers set honest expectations for "point it at an existing repo."
2. **Function-level acceptance skews short** (accepted-LOC% ≈ half of accepted-functions% in black): small pure helpers pass; long orchestration functions fire something. Verified-island adoption will be helper-first.
3. **The admission priority signal is clear and stable across corpora:** f-strings, `raise`, generators-consumed-eagerly, and common decorators would each buy meaningful coverage; the Tier 2 method surface dominates everything.
4. **Caveat, repeated:** `U-METHOD`/`U-CALL` optimism means true coverage is *lower* than reported once types land; the exclusion-rule fires (`X-*`, `T-*`, `F-*`) are the reliable part.

## Next

- basedpyright integration (types make `U-*` rules honest; adds `Any`-leak detection)
- Survey a stratified sample of strict-mode-clean packages beyond these three
- Wire rule-fire telemetry into the v1.5 admission decision in [ROADMAP.md](ROADMAP.md)
