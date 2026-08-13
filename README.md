# LemmaPy

> **Status: M0–M2 complete.** The pipeline runs end-to-end on the v1 fragment: `#@` specs parse ([grammar v0.2, frozen](docs/SPEC-GRAMMAR.md)), compile to runtime contracts that CrossHair searches for counterexamples, and translate to Dafny for SMT proofs (`lemmapy verify`). All four soundness layers are built — conformance checking (`lemmapy check`), boundary guards with the attack gallery demonstrably stopped (`lemmapy guard`), island integrity with assumptions A1–A7 in the verification report (`--report`), and continuous translation validation (`lemmapy difftest`, in CI on every PR). The M2 agent layer is live: structured failures (`verify --json`), the proof-repair loop (`lemmapy repair`), benchmark-derived repair exams, and an LSP (`lemmapy lsp`). Twelve corpus functions are proven — including `gcd` with its full maximality spec via the `#@ proof` lemma-sidecar mechanism — and scored 12/12 on [lemmapy-benchmark](docs/BENCHMARK.md)'s assurance ladder (42/42 mutants killed). Licensed under [MIT](LICENSE).

Developers (and LLM agents) annotate **production Python** with specifications in `#@` comments. The toolchain translates a precisely defined typed fragment into [Dafny](https://dafny.org/), where an SMT-backed verifier discharges the proofs — with LLM assistance for the ones automation misses. The Python file stays the source of truth: CPython ignores the annotations, and no code is rewritten in another language.

```python
#@ verified
#@ requires forall i in range(len(xs) - 1) :: xs[i] <= xs[i + 1]
#@ ensures result == -1 or (0 <= result < len(xs) and xs[result] == target)
def binary_search(xs: list[int], target: int) -> int:
    lo, hi = 0, len(xs)
    while lo < hi:
        #@ invariant 0 <= lo <= hi <= len(xs)
        #@ invariant forall k in range(lo) :: xs[k] < target
        #@ invariant forall k in range(hi, len(xs)) :: xs[k] > target
        mid = (lo + hi) // 2
        if xs[mid] < target:
            lo = mid + 1
        elif xs[mid] > target:
            hi = mid
        else:
            return mid
    return -1
```

## Try it

```bash
pip install -e ".[dev]"
```

Hunt for counterexamples at runtime (no proof needed — CrossHair searches the compiled `#@` contracts):

```bash
lemmapy hunt examples/clamp.py
```

This prints `false when calling clamp(-1, 0, 0)` — a concrete counterexample to the seeded bug in [examples/clamp.py](examples/clamp.py), found from the specs alone, with no test written.

Prove a function correct for **all** inputs (typed fragment → Dafny → SMT; requires [Dafny](https://dafny.org/) on PATH):

```bash
lemmapy verify examples/contact/he_humaneval_13.py --time-limit 60
```

That's Euclid's `gcd` verified against its full spec — divides both arguments *and* is the greatest such divisor — with the divisibility lemma pack supplied in a [`.proofs.dfy` sidecar](examples/contact/he_humaneval_13.proofs.dfy) referenced from a `#@ proof` clause. Failures map back to the Python source line.

Score the whole task corpus on the assurance ladder (gate → hunt → mutants → encode → prove → fidelity):

```bash
lemmapy benchmark
```

## Why this is not "just run a verifier on Python"

Python is dynamically typed, and a type checker's acceptance is not soundness. The project's central claim is that dynamic typing decomposes into four distinct threats, each answered by an independently checkable mechanism ([ARCHITECTURE.md](docs/ARCHITECTURE.md)):

| Threat | Mechanism |
| --- | --- |
| Code uses constructs with no defined Dafny meaning (`cast`, reflection, aliased mutation) | **Conformance checker** — allowlist-based fragment admission + ownership dataflow |
| Untyped callers pass values the proof never assumed | **Generated boundary guards** — deep type checks, executable preconditions, copy-in, blame |
| Runtime patching swaps out the verified code | **Island integrity** — runtime hardening + explicit assumptions A1–A7 |
| The Dafny model silently means something different from CPython (`7 // -2`, truthiness, aliasing) | **Translation validation** — continuous differential testing via Dafny's Python backend |

The result is a precise, honest guarantee: *verified properties hold for every execution entering through the generated guards with all executable checks passing, in programs the conformance checker accepts, under stated assumptions, with the encoder continuously cross-checked against CPython.*

## Design commitments (v1)

| Axis | Choice | Rationale |
| --- | --- | --- |
| Embedding | Shallow translation of a typed fragment | The prover sees an inspectable model of a clear fragment; no full-CPython-semantics claim |
| Typing | Typed island + checked boundary | Precise types where verified; generated guards keep guarantees when untyped code calls in |
| Backend | Dafny first; thin internal IR keeps a second backend open | Strongest SMT automation and LLM proof DX available today; executable Python backend enables differential testing |
| Spec surface | `#@` comment annotations on real Python | Production code stays the source of truth; zero runtime or import friction |
| Mutation | Value semantics under an explicit ownership discipline | Best prover/LLM fit; soundness restored by a checkable aliasing discipline, not assumed |
| Proof DX | Automation first, LLM proof-repair loop for the rest | design goal throughout |

## How this differs from adjacent work

- **[Strata-Python](https://github.com/strata-org/Strata-Python)** (AWS) — the nearest neighbor, one layer down: it translates Python into the Laurel IVL for SMT verification, but specs are machine-oriented serialized files, there is no protection for verified code called from untyped Python, and no proof-repair workflow. Laurel is a candidate *second backend* for this toolchain, not a substitute for it.
- **[Nagini](https://github.com/marcoeilers/nagini)** — proves the front-end shape works (typed Python, shallowly encoded into an IVL); this project trades its Viper permission logic for SMT/LLM automation and adds the boundary-guard and translation-validation layers.
- **[CrossHair](https://github.com/pschanely/CrossHair) / icontract / beartype** — the dynamic-checking ecosystem; used *by* this project (M0 compiles the same `#@` specs to runtime checks) rather than competed with.
- **TensorGuard / TorchLean** — domain-specific (tensor metadata / neural-network mathematics); this project verifies user-stated functional properties of general typed Python.

## Documentation map

| Document | Contents | Status |
| --- | --- | --- |
| [ARCHITECTURE.md](docs/ARCHITECTURE.md) | System architecture (components, data flow, trusted computing base, repo layout) and the soundness design (four layers, ownership rules, guard anatomy, assumptions A1–A7, lowering catalog) | ✅ (planned) |
| [ROADMAP.md](docs/ROADMAP.md) | Milestones M0 → v2 with exit criteria; backend watchpoints | ✅ |
| SUBSET.md | The versioned fragment definition (seeded from the lowering catalog) | planned |
| DECISIONS.md | Resolved design decisions with rationale and revisit tripwires | planned |
| RELATED-WORK.md | The verification landscape and positioning | planned |
| [SPEC-GRAMMAR.md](docs/SPEC-GRAMMAR.md) | The `#@` spec language: clauses, expression syntax, desugaring rules, decisions | ✅ (v0.2, frozen) |
| [GRAMMAR-CONTACT.md](docs/GRAMMAR-CONTACT.md) | The M0 exit exercise: 20 annotated HumanEval/MBPP tasks, mutation-tested; friction findings and the freeze decision | ✅ |
| [CORPUS-RESULTS.md](docs/CORPUS-RESULTS.md) | Fragment-coverage numbers: nine OSS repos + the HumanEval/MBPP greenfield contrast | ✅ |
| [BENCHMARK.md](docs/BENCHMARK.md) | lemmapy-benchmark: assurance-ladder scoring over annotated-Python tasks, mutant-panel spec strength | ✅ (v0) |
| [EVALUATION.md](docs/EVALUATION.md) | Research questions, the proof-completion benchmark family, measurement plan | ✅ (partial draft) |
