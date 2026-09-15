# Callable exact contracts and backward compatibility

`#@ ghost_ensures` is a Dafny postcondition whose proof may refer to defined
predicates in the adjacent `.proofs.dfy` sidecar. Unlike a final `#@ proof`
statement, it checks the value actually returned on every return path and
becomes a guarantee available at checked helper calls.

```python
#@ ghost_ensures ghost("Exact", xs, result)
def identity(xs: list[int]) -> list[int]:
    return xs
```

```dafny
predicate Exact(xs: seq<int>, output: seq<int>) { output == xs }
```

The sidecar and every implementation body are verified. Axioms, assumptions,
bodiless declarations and unchecked attributes remain forbidden. Ordinary
`ensures` continues to reject `ghost()`. `ghost_ensures` is header-only; Lean
explicitly rejects it. Runtime guards check supported preconditions and optionally ordinary
postconditions; they do not evaluate ghost predicates. Thus these are static guarantees, not
additional runtime checks.

Checked helpers may return read-only sequences. A returned sequence may alias
an argument: callers cannot mutate it, and a sequence-returning helper call
conservatively invalidates ownership of the caller's local sequences. This
prevents treating Dafny values as a license to mutate shared Python objects.

## Comparing annotated functions

```sh
python -m veripy.compatibility --old old.py --new new.py \
  --function convert --out build/fresh-comparison --backend dafny-outcomes
```

Or use `veripy.compatibility.compare(old, new, out, old_function="convert")`.
The output directory must be fresh. `--new-function` supports a different
implementation name. Parameter names, kinds and types must match. Keyword-only
parameters and matching immutable scalar literal defaults are supported. Defaults
must inhabit the exact admitted type (`True` is not an `int` default). Identical
defaults and kinds let the universal value comparison cover omitted arguments.
Changed defaults, variadics and decorators remain unsupported.

The generated product verifies both complete annotated modules and their
sidecars together, then proves:

1. Every input satisfying the old precondition satisfies the new precondition.
2. Both versions have the same modeled exception outcome.
3. On normal return, the returned values are equal.

The supported boundary types are exact Python `int`, `bool`, `str`, lists,
fixed tuples and matching declared closed frozen record snapshots, subject to
the selected encoder's fragment.
Inputs are compared in the same typed domain. `dafny-outcomes` models `ValueError`
and explicit subclasses. Both versions must resolve matching exception names and
hierarchies; their deterministic class tags are compared, with zero indicating
normal return. This compares modeled classes, not class-object identity.
Exception messages, object identity, resource consumption, concurrency and
whole-repository behavior are outside this theorem. Termination and safety
obligations in both encodings remain mandatory. A false old precondition gives
a vacuous conditional theorem; the report separately records admitted samples
and makes no claim that bounded sampling establishes domain nonemptiness.

For distinct recursive specifications, `--relation relation.dfy` supplies a
checked `CompatibilityRelation` lemma with the entry parameters. It can refer
to `Old` and `New` module definitions. The sidecar whitelist applies, its body
must verify, and its preconditions must hold at the product's call site.
There is no trusted relational assumption.

The comparison uses the same bounded module resolver as functional verification.
Each version has independently resolved constants and explicit dependency models,
recorded in the result. Unresolved imports and arbitrary initialization remain
unsupported. Module state must remain stable under the modeled environment.
Native replay remains narrower: function-only modules, now including literal
defaults and keyword-only calls. Missing replay evidence does not weaken the
product's proof obligations.

Reports distinguish `proved-compatible`, `behavioral-difference`,
`unsupported`, and `inconclusive`. Proof failure alone never means behavioral
difference. A bounded, isolated native replay must exhibit a differing outcome
or rejected formerly admitted input. Replay timeout produces no verdict of
equality. Reports retain frozen source/sidecars, hashes, the complete product,
prover identity and logs. Native replay is narrower than proof admission and
skips modules requiring imports/record initialization.

## Record snapshots

Matching closed record schemas are compared by field values. The product builds
bridges between the old and new record representations, including supported
nested fields and container values. It checks admission and returned value
observations under that snapshot relation. Schemas, signatures and defaults
must meet the comparison gate; this does not establish Python object identity,
shared mutable graph equivalence or a buffer-alias compatibility theorem.

The [record development results](../case_studies/evidence/record-compatibility.json)
retain two previously known unchanged-body controls separately from the original
ten-boundary checkpoint. They are not unseen algorithm rewrites. Lean functional
proofs of those components remain separate from the Dafny product proof.

## Runnable example

The [Django study](../case_studies/django/README.md) contains the historical base36
algorithm rewrite, its old and new implementations, checked support and relation
lemma. Reproduce the comparison from the repository root with a fresh output
path.

```sh
python case_studies/tools/run_compatibility.py \
  --projects django --out build/django-compatibility
```

The [Black study](../case_studies/black/README.md) is a separate component and
comparison boundary. Both studies identify their pinned upstream commits and
source preparation. A historical recorded verdict and a current rerun are
separate evidence.
