# VeriPy assurance argument

## Claim and boundary

A successful VeriPy report establishes that the selected backend accepted the
specified proposition about an emitted model. Applying that result to a Python
call also requires a correspondence between the admitted Python values,
operations, dependencies and observations and their encoded counterparts.
The complete correspondence has not been mechanized. This document states the
obligations and maps the available evidence without treating regression tests
as a soundness theorem.

Let `P` be a Python component, `E(P)` its encoded model, `D` the declared input
domain, and `R` the relation between Python states and model states. Let `Obs`
include the declared return value, modeled exception class and any explicitly
modeled mutations. Resource exhaustion, timing, unmodeled exception messages,
and unmodeled environmental effects are outside this observation scheme.

The intended functional assurance is conditional on the following obligations.

1. **Admission** establishes the exact types, supported operations and dependency
   configuration required by `R`. Static annotations alone do not enforce exact
   runtime types or prevent subclasses from overriding operations.
2. **Initialization** maps constants, dependency models, record snapshots and
   permitted aliases into corresponding initial states. A source-preserving
   declaration extraction is not a proof of whole-module initialization.
3. **Execution correspondence** relates each admitted Python execution to an
   execution of `E(P)` with the same declared observations. Arithmetic division,
   indexing, evaluation order, short circuiting, exception propagation, Unicode
   configuration and mutation all belong to this obligation.
4. **Specification correspondence** maps the source contract to the proposition
   actually checked, including every hypothesis. A verified conditional theorem
   cannot be reported as an unconditional one.
5. **Proof authority** excludes unchecked user assumptions and verifies the exact
   final generated artifacts with the selected backend. Artifact bindings prevent
   a report for one input or implementation from being reused for another.

If these obligations hold and the backend proves the translated contract over
`D`, then the corresponding Python observations satisfy the source contract on
`D`. This is the intended conditional argument, not a proved theorem about the
current implementation.

## Compatibility obligation

For a declared old domain `D_old`, compatibility requires that every admitted
old call is also admitted by the new interface and has the same declared
observations. Proving the two versions separately is insufficient. Their
contracts may leave different results possible.

The relational wrapper must establish new admission from old admission, retain
old preconditions, execute or characterize both sides, and prove observational
equality. A user-supplied relation lemma may not introduce a stronger hypothesis
unless the wrapper proves it from the original domain. Where records or mutable
buffers are involved, the initial state relation and permitted aliases must be
explicit. Matching two independently copied values is not a proof of arbitrary
shared-state behavior.

A native witness establishes a concrete difference only after replay on the
pinned Python declarations or integrations within the stated domain. Solver
failure, a timeout and an unsupported construct do not establish incompatibility.
Likewise finite native agreement does not establish universal compatibility.

## Evidence map

| Obligation | Implementation and controls | Remaining trust |
| --- | --- | --- |
| Source and dependency boundary | `veripy/frontend/closure.py`, `tests/frontend/test_dependency_closure.py`, closed module environment and dependency tests | Static extraction, modeled initializers, omitted enclosing-module effects |
| Admitted operations | `tests/frontend/test_conformance.py`, arithmetic, Unicode, regex, sequence and buffer regression suites | Correctness and completeness of handwritten semantic models |
| Source contract and permitted edits | `veripy/proofs/repair.py`, backend sidecar gates, `tests/proofs/test_repair.py`, and frozen study source/type/contract tests | Annotation parsing, specification adequacy and implementation of edit validation |
| Proposition and proof authority | `tests/lean/test_lean_audit.py`, backend sidecar gates and axiom audits | Backend implementation and audited declaration-policy implementation |
| Relational domain preservation | `tests/compatibility/test_callable_compatibility.py::test_relational_hints_are_proved_and_preconditions_checked`, `tests/compatibility/test_relational_records.py::test_record_precondition_narrowing` | Correct composition of frontend models and product construction |
| State and alias observations | `tests/compatibility/test_callable_compatibility.py::test_sequence_call_invalidates_owned_alias`, buffer and relational record controls | Snapshot stability, adapter correctness and excluded concurrency |
| Execution agreement | `tests/lean/test_lean_translation_audit.py::test_composed_control_flow_against_cpython`, native study replays and dedicated differential tests | Finite coverage, shared model errors and host-specific runtime behavior |
| Result binding and handoff | `case_studies/history.json`, historical sealed-release and prospective-study audits in the [research archives](RESEARCH-ARCHIVES.md) | Trusted local checker and artifact store, not hostile-evaluator signatures |

Independent backend checks provide useful diversity, but they share parts of the
frontend and therefore do not constitute independent proofs of translation
soundness. Python execution checks exercise a different implementation path but
cover only the recorded inputs.

## Runtime guards and research interpretation

A generated guard may enforce exact types, an admitted precondition, dependency
identities and a supported alias policy. Its existence does not mean a proof was
checked. A backend proof does not mean an arbitrary unwrapped Python call meets
those admission conditions. The public result must identify both the checked
scope and the runtime boundary used by an integration.

Agent assistance changes how candidate annotations and lemmas are produced. It
does not change what authorizes a proof result. The proof checker evaluates the
fixed target independently of the agent's success message. Requirement authoring
is a separate source of uncertainty. A model-reviewed contract may still omit an
important behavior, even when that contract is proved correctly.
