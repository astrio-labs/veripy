# Maintained proofs of production Python

Write ordinary Python with `# @` contract comments. The Python function remains
the code that runs. `veripy project generate` translates enrolled current source,
runs strict type analysis and Dafny, and saves deterministic proof artifacts.
`veripy project check` repeats the proof and rejects stale artifacts in CI.

Install the built wheel and the hash-pinned dependencies in
`requirements-project.lock`. Install Dafny 4.11.0 on PATH. Python 3.14 is required
for the included native Due example; the verifier does not rewrite Python syntax
for an older interpreter. Production packages do not import VeriPy.

```sh
uv pip install --require-hashes -r requirements-project.lock
uv pip install --no-deps dist/veripy-0.1.0a1-py3-none-any.whl
veripy project generate examples/source_contracts/veripy-project.json
veripy project check examples/source_contracts/veripy-project.json
```

The examples include a loop with a checked proof helper, a list transformation,
a frozen record, and a native timedelta method. Their executable Python is used
by the tests. Changing a list element or arithmetic result produces a failed
obligation with a source location. A harmless implementation edit may prove while
reporting `stale`; regenerate after reviewing that edit. The commands work from
another directory because paths resolve relative to the manifest.

## A project belongs to its maintainer

A v1 manifest declares source-discovery globs, required target IDs, each source
module/backend/function list, semantic dependencies, optional `.proofs.dfy`
companions, an artifact directory, and an exact Dafny version. See the complete
example manifest. Every discovered annotated module must be enrolled; empty,
duplicate, omitted, missing and unsupported targets cannot produce a green result.
This explicit enrollment is not automatic whole-program dependency discovery.

```sh
veripy project check veripy-project.json --json proof-result.json
veripy project generate veripy-project.json --update-enrollment
veripy project generate veripy-project.json --update-contracts
```

The update flags record an explicit maintenance decision, not authenticated human
approval. Protect contracts, enrollment, tool pins and CI invocation through code
review. Changing expected behavior to `True` is not a repair of the implementation.

Source and generated artifacts are separate from proof additions. Generation
never overwrites a companion proof file. False lemmas fail verification; unchecked
assumptions and unsupported proof escapes are rejected. Contract, external schema,
type-policy and proof-sidecar changes need explicit review before regeneration.

## What the backends establish

- `dafny` verifies the supported scalar, loop, collection and immutable-record
  fragment. Preconditions and loop invariants are explicit source contracts.
- `dafny-native` verifies admitted immutable methods with exact builtin integer
  and timedelta semantics, including checked overflow obligations. Shift and
  overflow checks follow Python's evaluation order, and short-circuiting forms
  around shifts (including chained comparisons) fail admission, as do
  special-method overrides and unsupported operations.
- `dafny-heap` checks a conservative effect abstraction of validate-then-commit
  functions. Borrowed writes, rejection exits, aliases and iteration failures
  come from the actual Python AST. Metadata branch outcomes are nondeterministic.
  External passive field/method schemas are trusted contracts, not inferred facts.
  Its rejection-frame and retained-identity checks are not proofs of business
  compatibility, arbitrary object methods, or termination.

The translator, admitted standard-library semantics, typechecker and prover are
trusted components. A proof is conditional on its declared input and environment
contracts. Unknown syntax, tool errors and timeouts are never successful proofs.

Actual framework effects require additional mandatory checks. The Due integration
uses a proved runtime ownership/admission core and real PostgreSQL callback and
rollback observations. The obligation integration proves the unchanged report
merge's effect structure and exercises real Pydantic rejection, identity and
accumulation histories. These checks deliberately remove compatibility guards,
bypass admission, and suppress failures to demonstrate that the whole repository
gate detects defects beyond each local theorem.

## Results and maintenance

The machine result distinguishes `verified`, `failed`, `unsupported`, `timeout`,
`type-error`, `tool-error`, `stale`, `enrollment-error`, and `contract-change`.
Only `verified` exits zero. Proof failures retain backend output and source maps.
`check` always verifies current source; the lock is a provenance and freshness
record, not a cached proof verdict. It records source/dependency/contract/compiler
and type-policy inputs. It does not claim a hermetic operating-system snapshot.

Review generated `.dfy` and `.map.json` beside the Python and proof additions.
Retain source mutants and independent runtime observations when extending support.
In particular, loop-carried aliases, key reassignment, exception causes, f-string
format expressions and iterator failures can carry effects, and optional-receiver
field reads and format specifications can fail after a write: the regression suite
checks these rather than assuming successful example proofs imply a sound frontend.

For the project API use `veripy.project.run_project(manifest, "check")`. The CLI is
the stable repository entry point; required native framework checks should be
orchestrated by a repository-owned command alongside it. Installing the verifier
alone does not install an application's database or prove its external services.
