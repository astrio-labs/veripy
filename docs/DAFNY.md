# Dafny backends

Dafny is VeriPy's default proof backend. VeriPy translates admitted Python bodies
and specifications into Dafny, then invokes Dafny's Boogie/Z3 verification path.
Checked `.proofs.dfy` sidecars provide auxiliary definitions and lemmas. The
Python implementation remains the source of executable behavior.

## Setup

Install VeriPy from the repository with the development dependencies described
in the [project README](../README.md). The research toolchain uses Dafny 4.11.0.
Installing VeriPy's Python dependencies does not install the Dafny executable.

With the .NET 8 SDK installed, the following matches the Dafny installation used
by the [CI workflow](../.github/workflows/ci.yml). The PATH command is for POSIX
shells. On Windows, add the .NET global tool directory to your user PATH.

```sh
dotnet tool install --global dafny --version 4.11.0
export PATH="$HOME/.dotnet/tools:$PATH"
dafny --version
```

If Dafny is already installed, check its version before changing the environment.
For comparable research runs, use Python 3.12.2, Unicode 15.0.0 and the default
4,300-digit integer conversion limit. The [archive guide](RESEARCH-ARCHIVES.md)
records the full frozen environment. Other host configurations can change
generated semantic models and must be reported separately.

## Verify a component

From the repository root, with the development environment active.

```sh
cat > component.py <<'PYTHON'
#@ ensures result == x + 1
def increment(x: int) -> int:
    return x + 1
PYTHON
veripy check component.py
veripy verify component.py --time-limit 30 --outdir build/component-dafny
```

The default CLI runs basedpyright before proof verification. `--no-types`
explicitly skips that gate. `veripy check` dry-runs the ordinary Dafny encoder,
so it is not the admission authority for every specialized backend.

## Select a Dafny backend

| Name | Intended use | Boundary |
| --- | --- | --- |
| `dafny` | Core functional verification | Partial operations generate safety obligations under the contract |
| `dafny-outcomes` | Functions with admitted exception behavior | Explicit modeled exception classes, hierarchy and restricted handlers |
| `dafny-buffers` | Admitted bytearray mutation | Declared alias policy and current/entry buffer observations |

The latter two require `--json` on the current CLI. For example, verify the
historical Django converter with its exact result contract and proof support.

```sh
veripy verify case_studies/django/compatibility/new.py \
  --backend dafny-outcomes --time-limit 60 \
  --outdir build/django-outcomes --json build/django-outcomes/result.json
```

This command proves one version's contract. It does not compare versions.
The [supported-fragment matrix](SUPPORTED-FRAGMENTS.md) records each backend's
evaluated scope, including restrictions on Unicode, dependencies and mutation.

## Specifications and checked proof support

Use `#@ requires`, `ensures`, `invariant` and `decreases` for the admitted
contracts and loop obligations. A `#@ proof LemmaName(...)` hook calls a lemma
from the adjacent sidecar. `ghost_ensures` can state a postcondition using a
defined sidecar predicate, checked on every return and available to callers.
These static ghost predicates are not evaluated by runtime guards.

The sidecar declaration policy excludes assumptions, axioms, bodiless proof
declarations and unchecked attributes. Every supplied declaration and generated
implementation obligation must pass. Editing a generated model instead of the
Python source or checked support does not update the source-bound proof.
See [specifications](SPEC-GRAMMAR.md) for syntax and [semantics](SEMANTICS.md)
for evaluation order, helper composition and alias requirements.

Structured results are available through `--json` or `from veripy import api`.
The [API guide](AGENT-INTERFACE.md) defines statuses, source diagnostics and
artifact handling. API proof operations do not implicitly run the CLI typing
gate. `--time-limit` controls the limit passed to Dafny; the driver also has a
separate process timeout. A timeout is an incomplete proof attempt, not a
counterexample. Use a fresh work directory when retaining a distinct run.

## Guards and execution checks

Generate a wrapper with exact-type checks, supported preconditions and optional
runtime postconditions.

```sh
veripy guard component.py --check-ensures --outdir build/component-guard
```

The guard backend must match the admitted source and observation policy.
Outcome guards support selected exception-aware checks. Buffer guards check
declared identities before mutation. Generating a guard does not establish
proof success or force callers to use the wrapper.

`veripy difftest` uses Hypothesis to compare original Python execution with a
Dafny model compiled back to Python. Its Python dependencies are included in
the development extras. The generic harness has its own admitted scope and
does not imply execution coverage for every outcome or buffer program.
CrossHair contract search through `veripy hunt` is another, separate check.
Finite agreement and absence of a found counterexample are not universal proofs.

## Compatibility, evidence and limits

The compatibility checker uses Dafny products to establish old-input admission
and equality of modeled observations. It checks both implementations and any
relation lemma. Use the [compatibility guide](CALLABLE-COMPATIBILITY.md) for
commands, matching record snapshots and verdict meanings.

The [paired inventory](../case_studies/components.json) contains 25 proof units
shared with [Lean](LEAN.md), with a separate Dafny backend choice for each unit.
Additional scoped Dafny examples cover calendar arithmetic, name normalization,
ETags and byte buffers. Proof obligations, helpers and composed units are not
independent repository samples. [Evaluation](EVALUATION.md) separates current
checks from historical measurements and preserved failures.

Dafny proof success concerns the emitted model. Applying it to Python also
requires correct translation, specification correspondence and the recorded
input/environment boundary. These obligations are not mechanized end to end.
The [assurance argument](ASSURANCE-ARGUMENT.md) describes the remaining trust.
