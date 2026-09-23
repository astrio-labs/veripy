# Your first proof

This tutorial uses the default Dafny backend. Complete [installation](installation.md) first and run commands from the repository root.

## Write a contract

Save this program as `component.py`.

```python title="component.py"
#@ requires x >= 0
#@ ensures result == x + 1
def increment(x: int) -> int:
    return x + 1
```

The precondition limits the claim to nonnegative integers. The postcondition relates the result to the argument. The contiguous annotation block must sit directly above `def`.

## Check admission, then prove

```sh
veripy check component.py
veripy verify component.py --time-limit 30 --outdir build/first-proof
```

`check` parses the annotations and checks admission through the ordinary Dafny encoder. It does not prove the postcondition. A successful `verify` run includes `VERIFIED (increment)` and exits with status zero. Generated paths may differ between runs.

Verification covers admitted inputs satisfying the precondition, rather than just a finite list of examples. Its connection to Python depends on the trusted translation and semantic boundary.

## Introduce a bug

Change the return statement to `return x + 2` and run verification again. The postcondition no longer follows, and this example should report `VERIFICATION FAILED` with a nonzero exit status.

Restore `return x + 1` before continuing. In general, failure to prove a contract can also mean missing proof support or a resource limit. Read [understanding results](results.md) before treating a failed proof as a demonstrated bug.

## Try the Lean backend

With Lean installed, run the same restored Python source through the Lean backend.

```sh
veripy verify component.py --backend lean   --json build/first-proof-lean/result.json --time-limit 30
```

Non-default backends require `--json`. The JSON report is a list of per-file results. The first result should have `status` equal to `ok`. Different backends do not support identical Python fragments or auxiliary proofs.

## Enforce a runtime boundary

Running `component.py` directly does not enforce its comments. To generate a wrapper, run

```sh
veripy guard component.py --check-ensures --outdir build/first-guard
```

Use the generated `component_guarded.py` wrapper when you want supported runtime checks. Existing callers are not automatically redirected to it. A guard checks its implemented conditions and does not replace a proof.

Next, learn [contracts and values](contracts.md).
