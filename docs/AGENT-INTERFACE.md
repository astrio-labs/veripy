# Agent interface

> **Status: stable surface, taxonomy version 1.** This is the
> contract for programs that consume LemmaPy — a repair agent, or a host
> embedding it as a proof backend. The human CLI output is not a contract;
> this is.

## Getting a structured outcome

```bash
lemmapy verify path/to/module.py --json failures.json
```

or, in process:

```python
from lemmapy.agentio import verify_structured
payload = verify_structured(Path("module.py"), Path("build/out"))
```

**Every outcome is a payload.** Spec errors, conformance rejections,
unreadable files, and prover crashes all return a record with a `status` —
never a traceback. Exit codes mirror it: `0` verified, `1` failed, `2` a
tool or input error.

## Payload shape

```json
{
  "schema": "lemmapy-failures/1",
  "file": "module.py",
  "toolchain": {
    "preamble_version": "0.5",
    "dafny_version": "4.11.0",
    "taxonomy_version": 1
  },
  "status": "failed",
  "functions": ["gcd"],
  "failures": [
    {
      "kind": "postcondition",
      "function": "gcd",
      "region": "source",
      "py_line": 24,
      "dafny_line": 71,
      "message": "a postcondition could not be proved on this return path"
    }
  ],
  "sidecar": {"path": "module.proofs.dfy", "exists": true,
              "lemmas": ["EuclidStepAll"], "text": "..."},
  "stub": null,
  "artifacts_kept": false
}
```

`status` is one of `ok`, `failed`, `spec-error`, `encode-error`,
`gate-error`, `tool-error`.

**Provenance.** `toolchain` rides *every* payload — including `gate-error`, which the CLI builds from the same `new_payload` skeleton, so a producer cannot omit it. `preamble_version` and
`taxonomy_version` are always present; `dafny_version` is `null` when the
prover was never reached (an unreadable source cannot have a prover
verdict, and asking for one would make an immediate error wait on a
subprocess).

**Artifacts.** Each call stages into a *private* directory: two concurrent
verifications sharing an `outdir` once raced on one stub path, so one
module could be verified against another's generated code. `stub` is the
generated `.dfy` path when `keep_artifacts=True`, and `null` otherwise —
never a path that has already been cleaned up. Nothing downstream reads
it; it is diagnostic only.

**Nullable attribution.** `region` is `"source"`, `"sidecar"`, or `null`.
`null` means the producer could not attribute the failure at all (a prover
run that failed without parseable diagnostics) — it is never a default or
a guess. Since `unknown` is routed by `region`, a fabricated attribution
would send a repair agent after the wrong file; treat a null region as
diagnostic output for a human.

**Coordinates.** `py_line` locates the failure in your source;
`dafny_line` locates it in the generated stub. A failure in the appended
proof sidecar carries `region: "sidecar"` and no `py_line`/`function` —
it belongs to no Python span, and must not be attributed to a function.

## The failure taxonomy

`kind` is the branching surface. It is versioned: `taxonomy_version`
changes when this set changes, so a host pinned to one vocabulary can
detect the change rather than silently mis-route an unfamiliar label. A
kind never appears in more than one group below — "the prover could not
prove it" and "we refused your input" must stay distinguishable.

Unrecognized kinds should be treated as `unknown` (unclassified), not
guessed at.

### Prover obligations — repairable by proof additions

The specs and source are correct as far as the toolchain knows; the
*proof* is incomplete. A repair agent may edit only the `.proofs.dfy`
sidecar.

| kind | what it means, and what to do |
| --- | --- |
| `assertion` | An executable `assert` in the source was not proved. |
| `bounds` | An index was not shown in range (Python's IndexError condition, modeled by PyIndex). |
| `call-precondition` | A callee's `requires` (often a preamble function's domain condition, e.g. PySeqMax on a possibly-empty sequence) was not established at the call site. |
| `division` | A divisor was not shown nonzero (Python's ZeroDivisionError condition). |
| `invariant` | A loop invariant failed on entry or was not maintained. |
| `postcondition` | An `#@ ensures` clause was not proved on some return path. Strengthen invariants or supply lemmas. |
| `resolution` | The proof sidecar does not typecheck — an unresolved name, a wrong argument count, or a wrong argument type. The proof was never attempted, so strengthening it is the wrong move: fix the declaration against the preamble signatures. This is the most common failure a repair engine actually hits (15 of 15 unclassified records in the first n=6 live run were of this kind). |
| `termination` | A `decreases` obligation failed; the prover cannot show the loop or recursion terminates. |
| `timeout` | The prover ran out of time or resources on this obligation. NOT a disproof: the property may still hold. |

### Front-end rejections — the source or specs must change

No proof addition helps: the input was refused before or during
translation.

| kind | what it means, and what to do |
| --- | --- |
| `conformance` | The construct is outside the verified fragment; the message names what and suggests an alternative. |
| `spec` | A `#@` clause is malformed or names something unknown. |
| `syntax` | The file is not parseable Python (or the spec-comment tokenizer failed on it). |
| `type` | The basedpyright strict type gate rejected the file. |

### Harness and exam failures — say nothing about the program

| kind | what it means, and what to do |
| --- | --- |
| `engine` | A repair/spec engine call failed (unavailable CLI, API error, wall exceeded). Says nothing about the program. |
| `freeze` | An exam's frozen region was modified — the attempt is invalid, not wrong. |

### Unclassified — origin undetermined

`unknown` is deliberately **not** a harness kind. The prover-message
classifier returns it for a diagnostic it does not recognize, and a failed
run with no parsed diagnostics reports it too — so treating it as
harness-only would make a host skip proof repair on a real (merely
unclassified) proof failure. Route it by `status` and `region`, not by
group.

| kind | what it means, and what to do |
| --- | --- |
| `unknown` | The producer could not classify this failure; the raw message is always attached. Origin is undetermined — use `status` (a `failed` run means the prover ran) and `region` to decide whether proof repair applies. A NULL `region` means even that could not be attributed: treat it as diagnostic output for a human, not as a repair target. Do not assume it is harness-only. |

## Stability contract

- Fields are **added**, never repurposed; `schema` bumps if one is removed
  or its meaning changes.
- The `kind` set is closed and published in `lemmapy/failures.py`. A kind
  reaching a caller without appearing there is a bug — a test scans the
  package for kind literals and fails on an undocumented one.
- Adding a kind bumps `taxonomy_version` and updates this file.
