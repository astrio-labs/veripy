# Shard validation semantics and limits

The selected source is PyTorch commit `2b3ec34829036a65cd9d1398ea72a0167dc37470`,
`torch/distributed/_shard/sharding_spec/_internals.py`, retained in the v1 source archive.
The executable ASTs of all five selected functions are unchanged. The complete
positive-width closure is documented in [closure/SEMANTICS.md](SEARCH-SEMANTICS.md). Only
parameter/return annotations, specification comments, and a snapshot record declaration
are added. This is a development case study, not a new benchmark or a held-out evaluation.

## Theorems

1. With equal offset/size ranks, the pair predicate returns true exactly when neither
   shard is separated from the other in any dimension by the source's two inequalities.
   The proof allows arbitrary integer coordinates. It returns true at rank zero.
2. For a nonempty list of equal-rank shards, `check_tensor` raises `ValueError` exactly
   when tensor rank differs, a shard's upper bound exceeds a tensor dimension, or the
   sum of shard volumes differs from the tensor volume. Otherwise it returns `None`.
   Product folds include the empty product of one. The theorem models exception class,
   not exception message, placement representation, traceback, or cause.

These facts alone do not prove nonoverlapping geometric coverage. For example,
`offsets=[2], sizes=[0]` and `offsets=[0], sizes=[5]` produce true from the pair
predicate even though one half-open interval is empty. The full validator has its own
zero-size special cases. `check_tensor` assumes nonoverlap was checked separately;
its equal-volume condition cannot itself detect duplicate shards plus gaps.

## Boundary and trust

Upstream `ShardMetadata` retains mutable lists. The integration boundary checks their
current exact types, ranks and nonnegative integer values, and copies them into frozen
records. Record fields are scalar lists. Guard generation then performs recursive
exact-type checks and copy-in. A frozen dataclass is not inherently deeply immutable.
The encoder rejects snapshot-field and borrowed-list mutation, including through
local aliases. It permits checked operations on fresh owned local lists, as needed
by the verified overlap searches.
Custom classes, list subclasses, booleans as integers, and simultaneous mutation during
snapshot/diagnostic replay are outside this boundary. Stable reads are an assumption,
not a proved concurrency guarantee.

Integer `math.prod(list[int])` lowers to a left-fold recursive product with empty value
one. `start`, custom iterables, and floating point products remain unsupported. Explicit
`None` and implicit fallthrough are modeled for None-returning outcome methods, with
no exposed `result` expression in their contracts. Exception-message expressions are
restricted to pure supported values and their indexing obligations remain checked.

## Real caller scope

The CPU environment installs Torch 2.8.0, not the selected complete 2.14 package. The
pinned helper module is loaded against actual Torch metadata classes; its validator is
patched into actual `EnumerableShardingSpec.__post_init__`, and the guarded tensor
check into `build_metadata`. That is a mixed-version source integration. No tensor
allocation, distributed communication, GPU kernel, or full PyTorch installation is
claimed verified. The closure adapter executes proved native pinned search bodies
on positive-width inputs, with explicit native fallback for zero-size overlap policy.

Two upstream metadata test method bodies are executed unchanged against real classes.
Their GPU skip decorators are removed because these bodies only construct metadata
and placement strings; this is not a pass of the complete upstream GPU test suite.
The adapter replays native failing tensor validation to retain the original error
message (including placement), after the guarded implementation establishes the
exception outcome. Both reads require stable inputs.

## Completed closure

The 1D search, ND sweep and dispatching validator now have checked proofs; see the
[closure evidence](README.md). The geometric claim excludes zero-size
shards, whose upstream behavior is preserved by an explicit counted native fallback.
The original two-function results remain archived as a historical milestone.
