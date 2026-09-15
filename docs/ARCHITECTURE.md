# Architecture

VeriPy verifies annotated Python components and separately checks compatibility
between versions. The source interface is Python with `#@` comments. Auxiliary
proofs live in checked backend-specific sidecars. Admission, proof success,
runtime checks and execution agreement are distinct results.

![VeriPy verification workflow](assets/veripy-workflow.png)

This guide describes the maintained implementation. The
[supported-fragment matrix](SUPPORTED-FRAGMENTS.md) identifies evaluated scopes,
and the [assurance argument](ASSURANCE-ARGUMENT.md) states the remaining trust.
Earlier design proposals are preserved in the
[documentation archive](RESEARCH-ARCHIVES.md#documentation-history).

## Source and admission

The frontend parses Python with CPython `ast` and parses specification comments
with VeriPy's annotation parser. A bounded resolver handles admitted module
constants, declarations and explicit dependency models. It does not execute
arbitrary imports to obtain proof facts or verify enclosing-module initialization.

`veripy check` performs a dry run of the ordinary Dafny encoder and then the
basedpyright type gate. It is not a universal admission check for all backends.
`veripy verify` checks types before invoking the selected backend. `--no-types`
explicitly skips typing, and `check --no-fragment` skips the encoding dry run.
Neither skipped check should be reported as passed.

Backend encoders are the authority for their admitted fragments. The separate
`veripy survey` command performs optimistic, untyped AST telemetry. Survey
acceptance does not establish admission or proof success.

Static annotations do not enforce exact runtime types. Python execution must
also meet the recorded input, dependency, alias and environment assumptions.
Generated guards enforce supported boundary conditions where they are used.

## Translation and proof checking

Dafny and Lean translate admitted Python ASTs directly. There is no shared
backend-neutral intermediate representation. Shared frontend code and models
mean the two backends are not independent proofs of translation correctness.

| Backend | Role | Important boundary |
| --- | --- | --- |
| `dafny` | Core functional verification through Dafny, Boogie and Z3 | Partial operations generate safety obligations |
| `dafny-outcomes` | Functional verification with modeled exception outcomes | Explicit exception hierarchy and restricted handler shapes |
| `dafny-buffers` | Functional verification of admitted byte-buffer mutation | Explicit alias policy and state observations |
| `lean` | Functional verification through generated Lean definitions and kernel-checked theorems | Selected arithmetic and imperative fragments, with checked exception behavior |

Generated artifacts are regenerated from source and specifications. Dafny proof
support is supplied in `<name>.proofs.dfy`, and Lean support in
`<name>.proofs.lean`. Each backend checks the declarations it accepts and the
obligations they discharge. Sidecars cannot replace the executable source with
unchecked code. Dafny rejects assumptions and bodiless proof declarations.
Lean rejects `sorry`, `admit` and other forbidden escape hatches and audits the
reported theorem dependencies. See [Lean](LEAN.md) for its permitted axioms.
The [Dafny guide](DAFNY.md) covers setup, backend selection and checked support.

Same-module helper composition, resolved dependencies, closed frozen records,
owned lists and sequence-returning helpers are admitted in particular fragments.
Their evaluation order, ownership and snapshot requirements belong to the
[semantics](SEMANTICS.md). A feature supported by one backend does not imply that
all backends accept the same program.

## Proof development and interfaces

Human and agent authors consume source-located diagnostics and supply candidate
proof support. The repair interface restricts edits to its admitted sidecar
surface and rechecks candidates. Its success message alone is not proof evidence.
The checked contracts and final generated artifacts determine the result.

The stable embedding surface is `from veripy import api`. API proof operations
and the research matrix are separate from the CLI's default typing gate. Hosts
must record any separately required admission and typing checks. The
[API guide](AGENT-INTERFACE.md) defines structured outcomes, failure categories
and artifact handling. The [editor guide](EDITOR.md) describes diagnostics and
proof-result invalidation after edits.

## Runtime boundary and execution checks

`veripy guard` generates supported wrappers around a preserved Python body.
The ordinary value boundary performs exact structural type checks, executable
precondition checks and copy-in for supported containers. Record snapshots and
resolved dependencies have additional checks. Outcome and buffer guards have
backend-specific policies. Buffer guards preserve the declared alias relation
rather than treating mutable arrays as independent copied values.

`--check-ensures` requests supported runtime postcondition checks. Static ghost
predicates are not evaluated by runtime guards. Guard generation neither proves
a contract nor forces callers to use the wrapper. Unwrapped calls must meet the
same proof assumptions by other means. Runtime mutation during snapshot creation
and hostile changes to Python internals remain outside the boundary.

`veripy emit` turns executable contracts into icontract checks. `veripy hunt`
uses CrossHair to search for contract violations. Absence of a found violation
is not a universal correctness result.

`veripy difftest` uses Hypothesis to compare original Python execution against
Dafny-compiled Python models. It exercises translation independently of proof
success. The generic harness and generated guards target Dafny. Lean execution
comparisons use dedicated tests and case-study replay. Finite agreement is
supporting evidence, not a compiler-correctness theorem.

## Compatibility and evidence

The compatibility checker verifies a product of two admitted versions. It checks
old-input admission in the new version, equality of normal results and equality
of modeled exception outcomes. Matching record schemas can be related through
value snapshots. Any auxiliary relation lemma must itself verify and satisfy its
call-site preconditions. See [callable compatibility](CALLABLE-COMPATIBILITY.md).

Reports distinguish proof success, a replayed behavioral difference, unsupported
inputs and inconclusive attempts. Functional verification of both versions alone
does not establish compatibility. Recorded source hashes, backend identity,
assumptions and logs bind results to their inputs. Historical study results
remain tied to their frozen compiler and environment.

## Trust and implementation map

The intended Python guarantee is conditional on source-to-model correspondence,
correct specification translation, admitted inputs and dependencies, and backend
proof authority. Frontend correctness is not mechanized end to end. Regression
tests, negative controls, kernel checks and differential execution address
different obligations in the [assurance argument](ASSURANCE-ARGUMENT.md).

The ordinary Dafny report retains assumption identifiers A1-A7. Their exact text
and discharge status are defined in
[`verification/report.py`](../veripy/verification/report.py). They cover stable
code and builtins, guarded entry, concurrent mutation, Python semantics, resource
and asynchronous exceptions, import integrity, and typing judgments. A generic
report does not replace a backend's more specific semantic boundary.

The [repository layout](REPOSITORY-LAYOUT.md) maps frontend, backends,
verification, proofs, guards, differential testing and editor code to directories.
The [evaluation guide](EVALUATION.md) separates engineering checks, component
proofs, historical comparisons and maintenance experiments.
