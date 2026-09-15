# Five-function proof boundary

The executable bodies of the pair predicate, 1D search, ND sweep, dispatcher and
`check_tensor` match the pinned upstream ASTs after erasing type annotations.
Comments, ghost calls, loop invariants and typed snapshot declarations supply proof
information without changing Python execution.

## What is proved

- The pair predicate returns exactly the source's dimension-wise inequality test.
- The 1D search returns valid distinct indices with overlap on the selected axis,
  or `None` exactly when that axis separates every distinct pair.
- The ND search returns valid distinct indices with overlap on every axis,
  or `None` exactly when no pair overlaps on every axis.
- The dispatcher raises `ValueError` exactly when a pair of positive-width boxes
  overlaps on every axis. Empty inputs and single shards are accepted; two scalar
  rank-zero shards overlap and are rejected.
- For nonempty equal-rank input, `check_tensor` raises `ValueError` exactly for
  rank mismatch, an upper bound beyond the tensor, or unequal total volume.
  Its integer theorem includes signed and zero values; the real adapter admits
  only nonnegative metadata and dimensions.

The search contracts require equal ranks and strictly positive sizes. The selected
axis must exist; the ND sweep requires a nonempty list of valid candidate axes for
multiple shards and at most `sys.maxsize` shards. The model pins `sys.maxsize` to
9223372036854775807 on this 64-bit host. Scalar rank zero is a point (empty product
one and vacuously true all-axis overlap).

## Zero sizes and real objects

Upstream zero-size policy is not geometric: identical empty shards can be accepted
at offset zero and rejected at nonzero offsets. The semantic audit records eight
boundary examples. The adapter explicitly falls back to unchanged native validation
when any width is zero; these calls are counted separately and are not covered by
the geometric theorem. Empty input and scalar inputs do not require this fallback.

Actual Torch metadata remain mutable. The boundary rechecks exact classes, exact
list fields, equal ranks and nonnegative exact integers, then snapshots the fields.
Generated guards check/copy those snapshots. Internal helper calls execute their
unchanged native bodies without repeated guards because their preconditions are
proved at call sites. Optional postcondition checks are for debugging and are
excluded from default overhead measurements. Reads must remain stable throughout
snapshot and native diagnostic replay; concurrency safety is not proved.

The encoder rejects writes to snapshot fields and borrowed lists. Sorting, insertion
and prefix deletion are admitted only on owned local lists. This is stronger than
relying on a frozen dataclass, which alone does not make list fields immutable.

## Trusted and checked components

Defined sidecar predicates are available through `ghost("Name", ...)` only in loop
invariants and proof-call arguments. They cannot appear in runtime contracts or
executable Python. Dafny checks their bodies, domains, types and every lemma call;
there are no assumed helper contracts or sidecar axioms. Nested input propositions
are shared through generated, defined predicates to stabilize quantified proofs.
The sidecar refers to these generated names, so compiler changes require reproof.

The shared Dafny sequence library proves sorting order/permutation, stable indexed
key order and bisect partition facts. Its recursive insertion-sort model is used for
semantic comparisons, not runtime performance claims. The deployed island runs
Python's unchanged upstream algorithms. Python-to-Dafny translation itself remains
part of the trusted implementation; differential tests are evidence, not a proof of
the entire compiler.

The runtime is Torch 2.8.0 CPU with selected newer pinned helper source. This is a
mixed-version metadata integration, not a full installation test of that revision.
No tensor arithmetic, GPU kernel or distributed execution is verified or timed.
