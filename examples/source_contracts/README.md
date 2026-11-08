# Editing and proving Python components

These are executable Python modules. They import no verifier package and need no
runtime decorator. `measurements.py` demonstrates a frozen record, an exact list
transformation, and an unbounded arithmetic loop. `measurements.proofs.dfy` defines
a reusable loop predicate and a checked step lemma. `pauses.py` implements a
separate two-level retry policy using native `timedelta` fields; the division
guard prevents overflow before doubling.

Install the development verifier from a local source checkout, using Python 3.14
and Dafny 4.11.0 on `PATH`:

```sh
uv venv --python 3.14 .venv
uv pip install --python .venv --require-hashes -r requirements-project.lock
uv pip install --python .venv --no-deps -e .
.venv/bin/veripy project generate examples/source_contracts/veripy-project.json
.venv/bin/veripy project check examples/source_contracts/veripy-project.json
```

Run commands from the VeriPy checkout. Manifest paths resolve relative to the
manifest, so the installed command also works from any other working directory
when given an absolute manifest path. Dafny is a separate tool; the Python extra
installs the pinned type checker. The native backend assumes exact builtin
`timedelta`/`int` field and parameter types and ordinary immutable dataclass
semantics. It proves source arithmetic and exception outcomes under those
conditions. It does not prove CPython, generated dataclass machinery or runtime
validation of annotations.

Change `value += stride` to `value = value + stride` and run `check`. The theorem
still proves, while the retained source binding becomes stale. Run `generate`
and review the artifact/lock diff, then run `check` again. Neither command writes
to `measurements.proofs.dfy`.

Change `value += stride` to `value += stride + 1`. Dafny rejects loop preservation.
Change the list's outer `min` to `max`: the exact element postcondition fails.
Remove the native saturation guard: the delay contract or overflow assertion
fails. Restore those changes before generating artifacts.

To maintain the contract itself, edit its source comments or checked sidecar,
then run `generate --update-contracts` and review the reported change. Enrollment
changes require `--update-enrollment`. These are explicit review boundaries;
local flags do not authenticate a reviewer. CI should only run `check` against
the committed artifacts and must never regenerate them automatically.

The tests in `tests/project/test_fresh_examples.py` run actual Python behavior,
prove all four functions with real Dafny, reject five source faults, and admit
two equivalent edits. Test development dependencies are separate from the
minimal project lock.
