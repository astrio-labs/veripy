# Contracts and values

Contracts state the relationship between admitted inputs and outputs. Write the requirement first, then check whether the implementation establishes it.

## Preconditions and postconditions

```python
#@ requires lower <= upper
#@ ensures lower <= result <= upper
#@ ensures result == min(max(value, lower), upper)
def clamp(value: int, lower: int, upper: int) -> int:
    return min(max(value, lower), upper)
```

`requires` is an assumption at entry. `ensures` is an obligation at each normal return. Multiple clauses must all hold. `result` denotes the return value in a postcondition.

The range postcondition alone permits many implementations. The equality specifies which value callers receive. Prefer exact behavior when compatibility depends on that behavior.

Do not strengthen a precondition merely to make a proof pass without checking the intended API. Doing so excludes callers from the guarantee.

## Types and Python values

Type annotations guide admission. Supported values include integers, booleans and selected sequence and record forms, with backend-specific restrictions. A proof over mathematical integers does not establish correctness for arbitrary objects implementing `__add__`.

Runtime boundary checks may require exact types. Python's `bool` is a subclass of `int`, but that does not make it an admitted integer in every VeriPy boundary. Consult the [semantics reference](../SEMANTICS.md).

## Logical expressions

Ordinary comparisons, arithmetic and supported builtins can appear in contracts. VeriPy also supports specification syntax such as

```text
A ==> B
A <==> B
forall i in range(len(xs)) :: xs[i] >= 0
exists i in range(len(xs)) :: xs[i] == result
```

Quantifier domains must be explicit and admitted. `forall` and `exists` desugar to Python-style `all` and `any`. Their bodies extend to the end of the expression, so use parentheses when combining them with other expressions.

## Entry values

`old(xs)` observes the entry value of parameter `xs` where supported. Its argument must be a bare parameter name. General expressions such as `old(xs[0])` are unsupported.

The existence of `old` does not authorize arbitrary mutation or aliasing. Those must also pass the selected backend's admission checks.

## Static and runtime meaning

CPython ignores every `#@` clause. Invariants and proof hooks are static proof support. Dafny's `ghost_ensures` permits checked proof-only predicates and is not a Lean annotation or runtime check.

For exact placement, operators and reserved names, see the [annotation grammar](../SPEC-GRAMMAR.md). Continue to [loops and invariants](loops.md).
