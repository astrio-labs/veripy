# VeriPy

> **Status: M0–M2 complete** on the v1 fragment. `#@` specs parse ([grammar v0.2, frozen](docs/SPEC-GRAMMAR.md)), compile to runtime contracts that CrossHair searches for counterexamples, and translate to Dafny for SMT proofs (`veripy verify`). All four soundness layers are built — encoder admission (`veripy check`), boundary guards (`veripy guard`), island integrity with assumptions A1–A7 in the verification report (`--report`), and continuous translation validation (`veripy difftest`, in CI on every PR). The M2 agent layer is live: structured failures (`verify --json`), the proof-repair loop (`veripy repair`), benchmark-derived repair and spec-writing exams, and an LSP (`veripy lsp`) that runs at two speeds — instant conformance diagnostics on every keystroke, prover verdicts on explicit request, expiring the moment the buffer changes ([docs/EDITOR.md](docs/EDITOR.md)). Sixteen corpus functions are proven — including `gcd`'s full maximality spec, `modp`'s modular-power spec and `sum_to_n`'s closed form via the `#@ proof` lemma-sidecar mechanism, and `isqrt`'s maximality spec with no proof additions at all — and scored 16/16 on [veripy-benchmark](docs/BENCHMARK.md)'s assurance ladder (62/77 mutants refuted by the specs, 81%; 13 more crash and 2 diverge under mutation — caught by the interpreter or the wall rather than by the specification, so reported separately and never credited). Licensed under [MIT](LICENSE).

Developers (and LLM agents) annotate a **typed Python fragment** with specifications in `#@` comments. The toolchain translates that fragment into [Dafny](https://dafny.org/), where an SMT-backed verifier discharges the proofs — with LLM assistance for the ones automation misses. The Python file stays the source of truth: CPython ignores the annotations, and no code is rewritten in another language.

The fragment is small on purpose: `int` / `bool` / `str` / `list` / `Optional`, structured control flow, and an ownership discipline on lists. It is a *generation target* for agent-written helpers, not a filter you point at an existing library. HumanEval/MBPP-style solutions sit around 65% in-fragment; idiomatic OSS libraries sit at 3–23% ([CORPUS-RESULTS.md](docs/CORPUS-RESULTS.md)).

```python
#@ verified
#@ requires n >= 0
#@ ensures result >= 0
#@ ensures result * result <= n
#@ ensures n < (result + 1) * (result + 1)
#@ ensures forall k in range(0, n + 1) :: k * k > n or k <= result
def isqrt(n: int) -> int:
    r = 0
    while (r + 1) * (r + 1) <= n:
        #@ invariant 0 <= r <= n
        #@ invariant r * r <= n
        #@ decreases n - r
        r = r + 1
    return r
```

That's integer square root, verified against its maximality spec with no proof sidecar (`veripy verify examples/isqrt.py`).

## Try it

```bash
pip install -e ".[dev]"
```

Hunt for counterexamples at runtime (no proof needed — CrossHair searches the compiled `#@` contracts):

```bash
veripy hunt examples/clamp.py
```

This prints `false when calling clamp(-1, 0, 0)` — a concrete counterexample to the seeded bug in [examples/clamp.py](examples/clamp.py), found from the specs alone, with no test written.

Prove a function correct for **all** inputs (typed fragment → Dafny → SMT; requires [Dafny](https://dafny.org/) on PATH):

```bash
veripy verify examples/isqrt.py --time-limit 30
veripy verify examples/contact/he_humaneval_13.py --time-limit 60
```

The second is Euclid's `gcd` verified against its full spec — divides both arguments *and* is the greatest such divisor — with the divisibility lemma pack supplied in a [`.proofs.dfy` sidecar](examples/contact/he_humaneval_13.proofs.dfy) referenced from a `#@ proof` clause. Failures map back to the Python source line.

Score the whole task corpus on the assurance ladder (gate → hunt → mutants → encode → prove → fidelity):

```bash
veripy benchmark
```

## Why this is not "just run a verifier on Python"

Python is dynamically typed, and a type checker's acceptance is not soundness. The project's central claim is that dynamic typing decomposes into four distinct threats, each answered by an independently checkable mechanism ([ARCHITECTURE.md](docs/ARCHITECTURE.md)):

| Threat | Mechanism |
| --- | --- |
| Code uses constructs with no defined Dafny meaning (`cast`, reflection, aliased mutation) | **Encoder admission** — allowlist lowering; `veripy check` dry-runs the encoder. Ownership-lite rejects `append` on a borrowed list. |
| Untyped callers pass values the proof never assumed | **Generated boundary guards** — deep type checks, executable preconditions, copy-in, blame |
| Runtime patching swaps out the verified code | **Island integrity** — verbatim island copy + explicit assumptions A1–A7 |
| The Dafny model silently means something different from CPython (`7 // -2`, truthiness, aliasing) | **Translation validation** — continuous differential testing via Dafny's Python backend |

The result is a precise, honest guarantee: *verified properties hold for every execution entering through the generated guards with all executable checks passing, in programs the encoder accepts, under stated assumptions, with the encoder continuously cross-checked against CPython.*

## Design commitments (v1)

| Axis | Choice | Rationale |
| --- | --- | --- |
| Embedding | Shallow translation of a typed fragment | The prover sees an inspectable model of a clear fragment; no full-CPython-semantics claim |
| Typing | Typed island + checked boundary | Precise types where verified; generated guards keep guarantees when untyped code calls in |
| Backend | Dafny first | Strongest SMT automation and LLM proof DX available today; executable Python backend enables differential testing. A backend-neutral IR (and a second backend) is a design commitment; the encoder currently emits Dafny from CPython `ast`. |
| Spec surface | `#@` comment annotations on real Python | The Python file stays the source of truth; zero runtime or import friction |
| Mutation | Value semantics under an explicit ownership discipline | Best prover/LLM fit; the encoder enforces ownership-lite (fresh vs. alias) today, not the full §3.2 dataflow pass |
| Proof DX | Automation first, LLM proof-repair loop for the rest | The repair loop edits only the `.proofs.dfy` sidecar |

## How this differs from adjacent work

- **[Strata-Python](https://github.com/strata-org/Strata-Python)** (AWS) — the nearest neighbor, one layer down: it translates Python into the Laurel IVL for SMT verification, but specs are machine-oriented serialized files, there is no protection for verified code called from untyped Python, and no proof-repair workflow. Laurel is a candidate *second backend* for this toolchain, not a substitute for it.
- **[Nagini](https://github.com/marcoeilers/nagini)** — proves the front-end shape works (typed Python, shallowly encoded into an IVL); this project trades its Viper permission logic for SMT/LLM automation and adds the boundary-guard and translation-validation layers.
- **[CrossHair](https://github.com/pschanely/CrossHair) / icontract / beartype** — the dynamic-checking ecosystem; used *by* this project (M0 compiles the same `#@` specs to runtime checks) rather than competed with.
- **TensorGuard / TorchLean** — domain-specific (tensor metadata / neural-network mathematics); this project verifies user-stated functional properties of the typed fragment.

## Documentation map

| Document | Contents | Status |
| --- | --- | --- |
| [ARCHITECTURE.md](docs/ARCHITECTURE.md) | System as built, soundness design (§1–§9), as-built vs. design gaps | ✅ (system half matches the tree) |
| [AGENT-INTERFACE.md](docs/AGENT-INTERFACE.md) | Embedding API, failure taxonomy, payload contract | ✅ |
| [EDITOR.md](docs/EDITOR.md) | LSP: keystroke conformance, on-request proof | ✅ |
| [SEMANTICS.md](docs/SEMANTICS.md) | Fragment big-step rules and simulation claim (not mechanized) | ✅ (preamble 0.6) |
| [SPEC-GRAMMAR.md](docs/SPEC-GRAMMAR.md) | The `#@` spec language: clauses, expression syntax, desugaring rules, decisions | ✅ (v0.2, frozen) |
| [GRAMMAR-CONTACT.md](docs/GRAMMAR-CONTACT.md) | The M0 exit exercise: 20 annotated HumanEval/MBPP tasks, mutation-tested; friction findings and the freeze decision | ✅ |
| [CORPUS-RESULTS.md](docs/CORPUS-RESULTS.md) | Fragment-coverage numbers: nine OSS repos + the HumanEval/MBPP greenfield contrast | ✅ (survey still untyped) |
| [BENCHMARK.md](docs/BENCHMARK.md) | veripy-benchmark: assurance-ladder scoring over 16 annotated-Python tasks, mutant-panel spec strength | ✅ (v0) |
| [EVALUATION.md](docs/EVALUATION.md) | Research questions; RQ1/RQ2/RQ4 measured; RQ3 and held-out repair still open | ✅ (partial draft) |
| SUBSET.md | The versioned fragment definition (seeded from the lowering catalog) | planned |
| DECISIONS.md | Resolved design decisions with rationale and revisit tripwires | planned |
| RELATED-WORK.md | The verification landscape and positioning | planned |
