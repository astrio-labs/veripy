# Lean backend and case-study parity

VeriPy can translate annotated Python to executable Lean and prove its contracts
with Lean 4.33.1. The maintained paired inventory contains 25 proof units across
seven projects, using one annotated Python source per unit with separate
backend proof support.
The [inventory](../case_studies/components.json) is the authority for unit names.
This is parity for that cohort, not a claim that every construct accepted by any
Dafny backend is also accepted by Lean.

For Dafny setup and backend selection, see [Dafny backends](DAFNY.md).

## Use

Install Lean 4.33.1 through elan and make `lean` available on PATH. No mathlib is
needed. The Lean driver enforces `time_limit` as a wall limit in seconds. Timeouts
are inconclusive proof attempts; the matrix runner adds an outer process-group
cap. From the repository root, use a fresh output directory.

```sh
python3 -m veripy verify case_studies/sglang/live_planner.py \
  --backend lean --json build/sglang-lean/result.json --time-limit 900
```

The current CLI requires `--json PATH` for non-default backends. The Python API is:

```python
from pathlib import Path
from veripy.api import verify

result = verify(
    Path("case_studies/pytorch/validation.py"),
    Path("build/lean-validation"),
    backend="lean", time_limit=900, keep_artifacts=True,
)
assert result["status"] == "ok", result["failures"]
```

The CLI performs its default typing gate before verification. The proof API
and case-study matrix do not independently establish that raw upstream typing
annotations pass basedpyright. Record required typing preparation separately.

`ghost_ensures` remains Dafny-only. Lean proof hooks and sidecar declarations
must satisfy the Lean interface rather than translating a Dafny lemma verbatim.

Proof support lives beside the Python source in `NAME.proofs.lean`. Source bodies
and `#@` contracts stay unchanged. Proofs are backend-specific: Dafny lemmas cannot
be pasted into Lean. These case-study packs contain substantial hand-developed
mathematics and directed proof scripts; their success is not a measurement of
unassisted automation or LLM repair effectiveness.

## What is implemented

The existing arithmetic encoder is retained. A typed imperative encoder handles
lists, integer tuples, frozen records, options, checked indexing and updates,
helper calls, branch-local state, nested loops, early returns, `break`, `continue`,
list comprehensions, sorting, binary insertion/search, and the admitted exception
paths used by the cases. Runtime `all`/`any` and boolean operations preserve
short-circuit evaluation. Python floor division and modulo use Lean's `fdiv` and
`fmod`, including negative operands; zero divisors are explicit errors.

The [exact Luhn checksum study](../case_studies/stdnum/README.md) adds
admitted tuple-generator materialization, reversed traversal, string identity
conversion, string comprehension iteration, checked substring lookup, positive
literal slice strides, and sums of integer pairs. The decimal checksum theorem
passes through both backends. The [check-digit round trip](../case_studies/stdnum/README.md)
now also proves the actual two-function composition. The retained validation
closure additionally admits its explicit custom
exception hierarchy and restricted single-handler try regions, with checked
class outcomes. This does not cover arbitrary Python exception handling.
Iterator reuse and tuple/list
cross-type equality remain rejected; this is not arbitrary generator support.

Strings are sequences of Unicode code points, including Python's surrogate values.
Decimal conversion is pinned to the host Python Unicode tables and integer-string
conversion limit. The Black proof/replay environment uses Python 3.12.2,
Unicode 15.0.0, and a 4,300-digit limit. Regenerating under a different Python can
change the model. Errors model exception classes and evaluation of admitted
payload expressions; exact exception messages, traceback identity, and formatting
cost are outside the specification.

Lean's `Std.Do.mvcgen` generates verification conditions for the executable model.
Finite loops use cursor invariants; supported while loops require invariants and a
decreasing measure. Strong exact-output theorems additionally cover Django base36
and Black's mapping/consumer composition. Whole-function proof hooks must prove the
exact generated theorem; they do not replace the executable function.

## Evidence and limits

The [case-study report](../case_studies/evidence/README.md) links the proof,
source-binding, replay, and negative-control manifests. The current paired
inventory has **25 proof units**, each checked with both
backends in the retained Linux cohort, yielding 50 backend invocations.
Repeated helper functions and composed closures are not independent benchmark
problems. Both original SGLang planner contracts are included even though their
executable function is identical.

Every successful Lean invocation must exit successfully and its reported axiom
footprint must stay within `propext`, `Classical.choice`, and `Quot.sound`. Sidecars
reject unchecked assumptions, `sorry`, `admit`, `native_decide`, unsafe/opaque
replacement code, and metaprogramming commands. Historical binding audits record
reuse of earlier successful kernel checks
only when regenerated artifact bytes match. That audit reuse is distinct from
the fresh invocations recorded by the maintained proof runner.

The Python-to-Lean compiler is still trusted software, tested by execution replay
and regression tests; its correctness is not itself mechanized. The proof applies
to the admitted typed domain and stated preconditions. Native framework calls,
SequenceMatcher, tensors/GPU kernels, concurrency, arbitrary Python objects,
reflection, and general exception handling are outside these proofs. Existing
runtime integration measurements remain measurements of the Python integrations;
this work does not establish a Lean runtime speedup or a new GPU overhead result.

Lean guard generation, a general Lean `difftest` CLI, and the backend-neutral IR are
not implemented by this work. The checked case-study replay scripts supply the
Lean execution comparisons. Unsupported syntax is rejected rather than silently
abstracted. Pin the Lean version: these proofs use the evolving `Std.Do` API.

## Hardening and shared support

The [hardening report](../case_studies/evidence/README.md) records the hidden-assumption injection fix, adversarial controls, pinned dual-backend CI, proof-size comparison, and a frozen-support transfer attempt. Sidecars must be closed declarations: ambient context commands such as `section`, `variable`, and `include` are rejected. Named packaged libraries can be included with `-- VERIPY LIBRARY arithmetic`, `allocation`, or `ranges`; arbitrary imports are not supported. Public kept-artifact reports now link per-invocation prover logs and axiom audits.
