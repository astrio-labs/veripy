# Native timedelta method pilot

This local fork adds an opt-in `dafny-native` backend for a restricted immutable
class fragment. It admits the actual `ExponentialDelay.__post_init__` and `at`
bodies from Due commit `1c6fb565c1d0d393bfe4bdd2ec95aac8bc8377ea`.
`original.py` is the frozen source. `retry_delays.py` adds specification and
proof-hook comments; the executable method ASTs are identical. The accompanying
Apache license is Due's original package license.

```sh
python -m veripy verify case_studies/due/retry_delays.py \
  --backend dafny-native --time-limit 20 \
  --outdir build/native-delay --json build/native-delay.json
```

Use Python 3.14 and Dafny 4.11.0. The local strict type-checker configuration sets
`pythonVersion` to `3.14`, since the complete source also contains Python 3.14
exception syntax. The backend does not change the default Dafny fragment.

The new frontend validates native operand types before lowering frozen dataclass
fields to snapshots. Exact builtin `timedelta` fields become bounded integer
microseconds. Native comparisons, timedelta floor ratios, integer multiplication,
`int.bit_length`, left shifts and literal `ValueError` outcomes are modeled.
Every admitted timedelta product must prove that it stays within the real
timedelta range. A negative shift produces a `ValueError` outcome even if the
source has no preceding guard. User sidecars and all semantic definitions are
checked by Dafny; assumptions, axioms and unchecked sidecars remain forbidden.

The admitted class has no inheritance, custom descriptors, mutable field writes,
decorated methods or dynamic rebinding. Only `dataclass(frozen=True)` with an
optional literal `slots` argument is accepted. Fields use exact builtin
`timedelta`, `int` or `bool` values. Methods have simple positional signatures,
typed int/bool parameters, branches, eager return expressions and literal
`ValueError` raises. General constructors, float arithmetic, mutable graphs,
Pydantic models, ORM calls and transactions remain unsupported.

The proof assumes stable module bindings and immutable snapshots with exact
builtin field/parameter types. Bypassing the constructor, monkeypatching and
resource exhaustion are outside the boundary. The verified constructor body
checks invalid field bounds; successful ordinary construction supplies `at`'s
business invariant. Generated dataclass machinery and CPython itself are trusted.
Exact builtin types and unmodified stdlib bindings are theorem-domain assumptions:
Python annotations do not enforce them, and this backend supplies no runtime
guard. Subclass instances and overridden arithmetic are outside the domain.
Overflow safety is proved rather than represented as an additional exception
outcome. Messages, exception identity and tracebacks are not observed.

Source AST preservation does not mechanize correctness of the new lowering.
Structured results expose source hashes, field units, original method locations
and lowered source. Separate replay compiles the proved Dafny model and compares
it with CPython. Passing finite replay is translation evidence, not an end-to-end
Python semantics theorem. Runtime guards and old/new compatibility products have
not been extended for this backend.

The arithmetic support reuses the upstream SGLang `FloorDivFacts` proof and adds
checked bit-length bounds, power monotonicity, capped-threshold, delay
monotonicity and saturation lemmas. These definitions prove the actual
bit-length/shift implementation; no repeated-doubling replacement is used.

Tests: `python -m pytest tests/fragments/test_native_timedelta.py`. They verify
the original bodies, reject no-cap and shifted-exponent source mutations,
accept the exception-type-equivalent removal of the negative-step guard, and
reject unsupported near neighbors. The separate user-requested follow-up report
and retained replay code live in `arms/veripy/followup` in the experiment workspace.
