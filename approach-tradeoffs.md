# Python verification approaches — tradeoffs

Design brainstorm for a practical verification toolchain for Python: developers write annotated production Python, and the tool translates a chosen fragment into a verification backend (Dafny, Lean, or similar).

The intended developer experience is in the same family as annotated-source toolchains (production code stays executable; specs live beside it; a prover checks the translation). Python is not TypeScript, so the right fragment, typing story, mutation model, and backend mix should be chosen for Python — not copied from another language’s toolchain.

Scores below are qualitative (0–10) for design discussion, not benchmarks.

**Criteria**

| Criterion | Meaning |
| --- | --- |
| Approachable DX | Annotate production Python; proofs beside code; avoid living in an ITP |
| Dafny fitness | How naturally the approach maps to Dafny |
| Lean fitness | How naturally the approach maps to Lean |
| Greenfield strength | New typed modules / LLM-written cores |
| Brownfield reach | Existing untyped or loosely typed code |
| Semantic trust | How believable the Python↔prover correspondence is |
| LLM proofability | How easy it is for LLMs to finish proofs |
| Ship speed | Time-to-useful-toolchain (higher = faster) |

---

## 1. Embedding strategy

### Shallow fragment translation

Choose a typed Python subset and lower it syntactically into prover constructs (methods, seqs, maps). Python remains production code; the prover sees a model of that fragment.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 9 | 9 | 7 | 9 | 4 | 7 | 9 | 8 |

**Wins**

- Approachable DX: annotate real Python, verify a clear fragment
- Dafny is a strong primary backend
- Encoder is inspectable; no need for full Python semantics
- Fits LLM-written greenfield cores well

**Tradeoffs**

- Cannot claim full CPython semantics
- Brownfield requires carving typed islands
- Library surface must be curated (axioms / models)

### Hybrid (shallow core + curated models)

Shallow lower for control flow and local data, plus an explicit stdlib/preamble for list/dict/str ops. Unsupported calls become extern/havoc with contracts.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 8 | 8 | 7 | 8 | 6 | 6 | 8 | 6 |

**Wins**

- Pragmatic escape hatches for real Python code
- Still Dafny-friendly for the verified core
- Brownfield hotspots can be specified at boundaries

**Tradeoffs**

- Trust story becomes a patchwork of models
- Risk of axiom creep hiding bugs
- More engineering than pure shallow v1

Still not a deep embedding: Dafny stays viable if every modeled/extern surface is documented.

### Deep embedding of Python

Encode Python AST/operational semantics in the prover and prove properties about that semantics. Closest to “real Python,” farthest from approachable toolchain DX.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 3 | 2 | 8 | 4 | 7 | 9 | 3 | 2 |

**Wins**

- Strongest story for faithfulness to Python
- Better long-term research substrate in Lean
- Can reason about features shallow models exclude

**Tradeoffs**

- Dafny is a poor host for deep embeddings
- LLM proof workflows get much harder
- Developer experience drifts toward ITP expertise
- Years of semantics work before useful DX

If this is the goal, prefer Lean (or another semantics-friendly host) over Dafny.

---

## 2. Typing front-end

How much static type information the toolchain requires before translation. This axis matters more for Python than for TypeScript: Python is gradually typed in practice, and much existing code has weak or missing annotations.

### Typed subset required

Verified functions must have precise annotations; reject `Any` / unannotated. Use Pyright or mypy as the type front-end for the verified fragment.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 8 | 9 | 8 | 9 | 3 | 8 | 8 | 8 |

**Wins**

- Resolve/narrow passes become tractable
- Translation to Dafny types is mostly mechanical
- Matches a greenfield / LLM-Python thesis

**Tradeoffs**

- Brownfield untyped code is out of scope until typed
- Users may feel the subset is “not real Python”

### Gradual typing islands

Require types only on the verified island; the rest of the repo can stay untyped behind runtime contracts.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 8 | 8 | 7 | 8 | 7 | 7 | 7 | 6 |

**Wins**

- Best adoption path for real Python codebases
- Incremental path: verify a core, wrap the boundary
- Keeps Dafny viable inside the island

**Tradeoffs**

- Boundary contracts become load-bearing
- Type inference gaps still block verification
- More product surface (contracts runtime)

### Untyped / dynamically typed OK

Accept unannotated Python and infer or over-approximate types. Maximizes brownfield claims; stresses embedding and backends.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 4 | 3 | 6 | 5 | 9 | 4 | 4 | 3 |

**Wins**

- Largest addressable existing Python corpus
- Stronger story for brownfield adoption

**Tradeoffs**

- Translation becomes speculative / imprecise
- Dafny fit collapses without stable types
- Pushes toward deep embedding or heavy analysis

---

## 3. Backend strategy

### Dafny primary

Strong automation, LLM-friendly proof style, regeneratable stub plus additions-only proof file.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 9 | 10 | 2 | 9 | 5 | 7 | 9 | 8 |

**Wins**

- Best LLM verification DX among common options today
- Early spike path already exists (e.g. veripy-style `#@` → Dafny)
- Clear regen/proof-addition workflow

**Tradeoffs**

- Poor host for deep embeddings
- Weaker for heavy inductive mathematics
- Must accept fragment + model limitations

### Lean primary

Richer proof language and better deep-embedding substrate; harder automation and LLM workflows than Dafny for many program proofs.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 6 | 1 | 10 | 6 | 6 | 8 | 5 | 4 |

**Wins**

- Best if the research goal is semantics faithfulness
- Inductive proofs and libraries are stronger
- Aligns with Metareflection / Lean ecosystems

**Tradeoffs**

- Harder path to approachable, LLM-assisted program proofs
- More moving parts in the proof stack
- Slower time to a usable developer toolchain

### Viper / Nagini-style

Python-oriented verification research (permissions, heap). Closer to real Python objects; different tooling culture from Dafny/Lean program-proof workflows.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 5 | 2 | 3 | 6 | 7 | 8 | 4 | 4 |

**Wins**

- Designed around Python/object semantics
- Stronger story for mutable heap programs
- Existing research (Nagini) to learn from

**Tradeoffs**

- Different ecosystem and skill transfer than Dafny-centric work
- LLM proof workflows less established
- May optimize for heap fidelity over approachable DX

### Shared IR, multi-backend

One annotated Python source, shared pipeline, emitters for Dafny now and Lean (or others) later. Highest long-term leverage, more IR discipline.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 9 | 8 | 8 | 8 | 5 | 7 | 8 | 5 |

**Wins**

- Keeps backend choice open as the Python fragment stabilizes
- Forces clean fragment/IR thinking early
- Lets Python-specific lowering differ per backend where needed

**Tradeoffs**

- Overbuild risk if v1 only needs Dafny
- IR must stay mostly backend-neutral (harder)
- Slower first demo unless scoped carefully

---

## 4. Spec surface

### `#@` comment annotations

Specs are comments; CPython ignores them. No new syntax, no erasure language. Natural fit for a “annotate the real file” workflow.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 10 | 8 | 8 | 9 | 7 | 8 | 8 | 9 |

**Wins**

- Production Python stays the source of truth
- Zero runtime / import friction
- LLMs already emit comments easily

**Tradeoffs**

- Specparser is a separate language island
- IDE support is custom unless you build it

### Decorators / `typing.Annotated`

Use `@requires` / `@ensures` or Annotated metadata. More idiomatic to Python’s existing tooling culture, but mixes runtime and ghost concerns carefully.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 6 | 7 | 7 | 7 | 6 | 7 | 6 | 6 |

**Wins**

- Feels native to Python developers
- Can share surface with runtime contract libraries

**Tradeoffs**

- Ghost/spec purity gets muddy
- Decorator evaluation / import side effects
- Harder to keep specs invisible to ordinary execution

### New surface language → Python

A verified dialect that erases/compiles to Python. Can restrict the language by construction, but usually harms adoption.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 4 | 7 | 7 | 6 | 2 | 5 | 6 | 2 |

**Wins**

- Can bake verification keywords into syntax
- Can restrict the language by construction

**Tradeoffs**

- Three languages problem (dialect + Python + prover)
- Erasure trust gap
- Parser/toolchain burden unrelated to proofs
- Brownfield nearly impossible

---

## 5. Heap / mutation model

How the toolchain treats Python’s mutable objects in the prover. This is a Python-shaped decision: lists, dicts, and aliasing are central to idiomatic code in a way that differs from more value-oriented fragments in other languages.

### Value / sequence semantics

Model list/dict updates as functional seq/map updates. Alias freeness assumed or enforced by fragment rules.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 8 | 9 | 8 | 9 | 3 | 6 | 9 | 9 |

**Wins**

- Best Dafny/LLM fit
- Simplest mental model for early demos
- Fastest path to working examples

**Tradeoffs**

- Diverges from Python aliasing reality (`a = b; b.append(1)`)
- Rejects many idiomatic mutable patterns

### Limited local mutation

Allow mutation of locally owned structures; forbid or havoc escaping aliases. Middle ground for realistic algorithms.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 7 | 7 | 7 | 8 | 5 | 7 | 7 | 6 |

**Wins**

- Covers many practical loops/algorithms
- Still mostly Dafny-method friendly
- Clear ownership rules can be taught

**Tradeoffs**

- Need precise fragment rules for aliasing
- More transform complexity than pure value model

### Full heap / object model

Track references, fields, sharing. Closest to Python objects; pushes toward Viper-style permissions or a deep Lean heap.

| DX | Dafny | Lean | Greenfield | Brownfield | Trust | LLM proofs | Ship speed |
| -: | ----: | ---: | ---------: | ---------: | ---: | ---------: | ---------: |
| 4 | 3 | 7 | 5 | 8 | 9 | 3 | 2 |

**Wins**

- Highest semantic fidelity for OO Python
- Brownfield object code becomes in-scope

**Tradeoffs**

- Dafny becomes awkward quickly
- Proof burden explodes
- Approachable DX largely lost

---

## Named combinations (presets)

| Preset | Embedding | Typing | Backend | Surface | Heap | Why |
| --- | --- | --- | --- | --- | --- | --- |
| Approachable v1 (recommended) | Shallow | Typed required | Dafny | `#@` | Value | Maximize DX and Dafny/LLM fit; defer brownfield breadth |
| Pragmatic islands | Hybrid | Gradual | Multi-backend | `#@` | Limited mut | Keep approachable DX while admitting real-code escape hatches |
| Semantics-first research | Deep | Gradual | Lean | `#@` | Full heap | Maximize faithfulness; accept slower DX |
| Python-heap native | Hybrid | Gradual | Viper | Decorators | Full heap | Optimize for mutable object programs |

---

## Cross-cutting hard choices

| Tension | Pole A | Pole B | If you want approachable Python DX… |
| --- | --- | --- | --- |
| Faithfulness vs approachability | Deep embedding / full heap | Shallow fragment / value or limited mut | Choose Pole B; document the semantic gap |
| Dafny vs Lean | LLM-friendly program proofs | Semantics & induction power | Dafny primary; Lean optional later via shared IR |
| Greenfield vs brownfield | Typed verified cores | Untyped existing repos | Greenfield fragment first; brownfield via islands + contracts |
| Comments vs new language | `#@` (or light decorators) on real Python | Erasing dialect | Prefer annotating real Python |
| Product vs research substrate | Toolchain developers can use | General Python semantics in a prover | Product cut first; keep research questions explicit |

### Combinations that conflict

- **Deep embedding + Dafny** — high conflict; Dafny is a poor host for deep embeddings
- **Shallow translation + untyped OK** — resolve/emit become guesswork; weak trust
- **Full heap + Dafny** — possible in niches, but fights automation/LLM advantage
- **Typed required + value semantics** — strongest approachable dual; weakest brownfield claim
- **Lean + shallow fragment** — viable, but may pay Lean complexity without deep-semantics payoff
- **Hybrid + gradual islands** — pragmatic research/product compromise for lab + real code

---

## Where Python should diverge on purpose

These are places a Python-best design should *not* blindly mirror a TypeScript-oriented toolchain:

- **Typing is optional in the wild.** Gradual islands and boundary contracts matter more for adoption.
- **Mutation and aliasing are core.** Limited local mutation may be a better default than pure value semantics.
- **Ints are unbounded; floats and objects are the hard parts.** Numeric modeling differs from JS `number`.
- **Exceptions, iterators, dataclasses, and stdlib richness** may deserve first-class fragment decisions rather than late add-ons.
- **Decorator/contract culture** is native to Python; comment annotations are still attractive, but decorators are a real alternative, not a curiosity.

---

## Working recommendation

Start the design doc around a Python-best, approachable cut:

- **Embedding:** shallow (or lightly hybrid)
- **Typing:** types required on verified code; gradual adoption at boundaries for real repos
- **Surface:** `#@` annotations first; revisit decorators if Python ergonomics demand it
- **Backend:** Dafny-first, with IR room for Lean later if needed
- **Heap:** prefer limited local mutation if the fragment must feel like Python; otherwise value semantics for the fastest v1

Treat deep embedding and full-heap Python as an explicitly alternate research track, not the v1 product claim.
