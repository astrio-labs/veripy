# Compare two versions

Proving two functions against separate contracts does not establish that existing callers see the same behavior. Compatibility needs a relation between versions.

## Prepare the implementations

Save the old implementation as `old.py`.

```python title="old.py"
#@ requires x >= 0
#@ ensures result == x + 1
def increment(x: int) -> int:
    return x + 1
```

Save the new implementation as `new.py`.

```python title="new.py"
#@ requires x >= 0
#@ ensures result == x + 1
def increment(x: int) -> int:
    return 1 + x
```

Run the comparison using Dafny's outcome model.

```sh
python -m veripy.compatibility --old old.py --new new.py   --function increment --backend dafny-outcomes --out build/increment-comparison
```

Use a fresh output directory for each comparison. The successful verdict is `proved-compatible`.

## What is checked

Within the admitted typed domain and environment, the product checks that old inputs remain admitted, modeled exception outcomes agree, and normal return values are equal. Both implementations and their proof support must also verify.

Changing the new precondition to `x > 0` excludes the formerly admitted input zero. Changing the new result to `x + 2` changes behavior. These are different compatibility failures.

A failed product proof alone is not a behavioral counterexample. The report uses `behavioral-difference` only when native replay witnesses a difference. Otherwise unsupported cases or unsuccessful proof attempts receive distinct verdicts.

## Apply this to your code

Parameter names, kinds and types must match, along with admitted defaults. Start with function-only modules. General dependencies and state introduce additional boundaries, and native replay is narrower than proof admission.

For exact contracts, relation lemmas, exception observations and report fields, see [callable compatibility](../CALLABLE-COMPATIBILITY.md). For a larger maintained example, run the Django comparison described in the [case studies](case-studies.md).
