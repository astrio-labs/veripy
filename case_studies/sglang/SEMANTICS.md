# Planner fragment and boundary argument

This is an implementation-level preservation argument, not a mechanized theorem
for VeriPy or a proof of SGLang's scheduler. The verified function retains every
upstream executable statement and its docstring. Its signature adds precise
types and its comments add contracts, invariants and checked ghost calls.

## Record snapshots

The new fragment admits closed, acyclic `@dataclass(frozen=True)` declarations.
Fields are exact scalar types or earlier frozen records. Inheritance, custom
methods, defaults, descriptors, mutable field types, recursive schemas and
module initialization/rebinding are rejected. Reads lower to fields of Dafny
datatypes. Constructing records inside verified bodies is not admitted in this
slice. Record arguments and returned records have a compiled runtime adapter;
method-call composition across record-valued boundaries remains outside M0's
scalar call boundary.

The generated guard binds the actual record classes and checks exact class
identity and every nested scalar field, rejecting Boolean values where integers
are required. It constructs fresh records and lists recursively. Aliases in the
input need not retain object identity: identity observations on these objects
are rejected by the encoder. Their scalar values must retain behavior. A host
must not replace class behavior or mutate the input during check/copy; the
generated island does not provide synchronization against hostile Python code.

The SGLang adapter reads `kv_committed_len` and `kv_allocated_len` into this
representation before invoking the guard. The two reads must observe stable
request state. This is an explicit restricted boundary, not a claim that
SGLang's mutable `Req` and `ReqKvInfo` classes are frozen. The experiment executes
the unmodified pinned `ReqKvInfo` class and uses `SimpleNamespace` request
envelopes as unit fixtures. It does not instantiate the full request/scheduler
stack or run `eagle_prepare_for_decode`.

## Lists and indexed writes

Singleton scalar-literal repetition such as `[0] * n` creates a fresh sequence
of length `max(0, n)`. Repeated nested mutable values and arbitrary repeated
expressions remain rejected. Restricting the repeated element to a literal
avoids moving a potentially failing element computation under a zero-length
sequence constructor. It also avoids modeling shared inner mutable objects as
independent values.

Indexed assignment is admitted only for a fresh, unaliased local scalar list
that is not being iterated. Escaping a list through direct aliases, tuple/list
containers or other list-valued assignments forfeits ownership. Parameter writes,
record writes, nested mutable element writes and walrus rebinding in write
expressions are rejected. The RHS is evaluated before the target index; values
are captured before a sequence update. `PyIndex` preserves Python negative
index normalization and adds bounds obligations. A verified program cannot
reach an out-of-bounds write under its contract.

## Enumerate and the proof

`for i, r in enumerate(reqs)` snapshots the stable input sequence and uses a
hidden increasing index. At the loop head, an invariant's `i` denotes the next
index and hence the length of the processed prefix. Inside the body it is the
Python enumerate index; `r` is the current element. Invariants cannot reference
`r`, which is not yet bound at the head. Neither target may be used after the
loop or reassigned in its body. Custom starts/keywords and non-list iterables
remain rejected. Existing continue handling advances the hidden index.

The planner invariant states exact correspondence for each processed request,
plus the difference between the two output prefix sums. `AllocationFacts`
proves the rounding, maximum and alignment properties from checked integer
division facts. `PrefixWriteSum` connects each sequence update to the next prefix
sum. `FullSlice` connects the final prefixes to the full outputs. These lemmas
have bodies checked in the same Dafny module; no assumed contracts are added.

Methods containing indexed writes use Dafny's `isolate_assertions` attribute.
It splits verification obligations and does not remove assertions or change
execution. This made a failed full-sum postcondition visible after the initial
combined proofs timed out. The missing connection was supplied by a checked
lemma. Compilation disables single-constructor wrapper erasure so record
adapters match Dafny's generated representation; this is a compilation setting,
not an alternative implementation of the planner.

## Scope of correctness

For a stable exact list of snapshots satisfying the four entry requirements,
the verified planner returns the exact ordered existing/next lengths and total
increment, never shrinks allocation, reserves sufficient capacity and maintains
page alignment. The proof is unbounded in batch size and integer magnitude;
runtime experiments are finite. Python resource exhaustion and asynchronous
exceptions are excluded as in the existing VeriPy model.

The experiment's original-source, snapshot, compiled and guarded executions,
mutation controls and boundary rejection tests support this argument. They do
not prove the adapter for arbitrary descriptors, concurrent allocation,
GPU/tensor operations, scheduler-wide OOM freedom, or a repair advantage.
