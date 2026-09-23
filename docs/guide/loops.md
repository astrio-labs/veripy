# Loops and invariants

A loop invariant describes what remains true as a loop progresses. It connects individual iterations to the function's final contract.

Save the following as `count.py`.

```python title="count.py"
#@ requires n >= 0
#@ ensures result == n
def count(n: int) -> int:
    total = 0
    for i in range(n):
        #@ invariant total == i
        total += 1
    return total
```

Run the default backend.

```sh
veripy verify count.py --time-limit 30 --outdir build/count
```

## Why the invariant works

At the first iteration, both `total` and `i` are zero. An iteration increases `total` by one, keeping it aligned with the next loop index. When all `n` iterations finish, the accumulated value is `n`.

The verifier generates obligations for initialization, preservation and the loop's exit. An invariant is something to prove, not an assumption you can insert unchecked.

Change the update to `total += 2`. The preservation obligation should fail. Restore the update before continuing.

## Placement and termination

Put loop invariants at the beginning of the loop body, before executable statements. An invariant nested inside a conditional does not describe the loop head.

Supported `while` loops also need the required termination argument, commonly a decreasing measure. The precise admitted form varies by backend. Parsing `decreases` does not mean an arbitrary Python loop is supported.

Loops with mutation, early returns or helper calls may need stronger invariants or checked lemmas. Start from a supported form and consult [fragment coverage](../SUPPORTED-FRAGMENTS.md) before adding proof machinery.
