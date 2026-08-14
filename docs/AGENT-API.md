# The agent API — `lemmapy-failures/1`

The machine contract. `verify_structured` returns it, `lemmapy verify --json`
writes it, and the proof-repair loop consumes it. **An embedding host should
key on this document, not on message text** — messages are prose and may be
reworded; ids and keys are the stable surface.

## Payload

| key | type | meaning |
| --- | --- | --- |
| `schema` | str | `"lemmapy-failures/1"` |
| `file` | str | the path as the caller spelled it |
| `status` | str | see below |
| `functions` | list[str] | spec'd functions found in the module |
| `failures` | list[record] | never empty for a non-`ok`, non-`tool-error` status |
| `sidecar` | object \| null | `{path, exists, lemmas, text}` |
| `stub` | str \| null | emitted Dafny; **null unless `keep_artifacts`** |
| `artifacts_kept` | bool | whether `stub` names a live file |
| `error` | str | present only for `tool-error` |

### `status`

| value | meaning | retry? |
| --- | --- | --- |
| `ok` | verified | — |
| `failed` | the prover did not discharge an obligation | no — the code or spec must change |
| `spec-error` | the `#@` specs do not parse | no |
| `encode-error` | the module is outside the verifiable fragment | no |
| `gate-error` | the type gate rejected the module | no |
| `tool-error` | the environment is broken (prover missing, unreadable file) | **yes** — this is the only retryable status |

`tool-error` is the distinction an integrator must not lose: everything else
is a verdict about the code, and retrying it changes nothing.

## Failure record

Every record has every key, for every status. Absent information is `null`
rather than a missing key, so a consumer written against one status cannot
`KeyError` on another.

| key | type | meaning |
| --- | --- | --- |
| `kind` | str | `postcondition`, `invariant`, `assertion`, `call-precondition`, `termination`, `timeout`, `bounds`, `division`, `conformance`, `syntax`, `spec`, `type`, `unknown` |
| `rule` | str \| null | stable id for `conformance` rejections (below); `null` for prover failures |
| `function` | str \| null | enclosing spec'd function |
| `region` | str | `source` or `sidecar` — which artifact the failure is in |
| `py_line` | int \| null | Python line |
| `dafny_line` | int \| null | line in the emitted stub |
| `message` | str | human prose; **do not parse** |

## `rule` ids

Set on every `conformance` (fragment-rejection) record. Specific ids are
added over time; a caller that does not recognise one should fall back to
the `unsupported-*` prefix, which is stable.

| id | meaning |
| --- | --- |
| `indexed-assignment` | `xs[i] = ...` — rebuild the list instead |
| `attribute-assignment` | `obj.field = ...` — the fragment has value semantics |
| `chained-assignment` | `a = b = ...` |
| `unsupported-assignment` | some other assignment form |
| `unsupported-type` | a type outside int/bool/str/list[T]/Optional[T] |
| `unsupported-call` | a call the encoder has no model for |
| `unsupported-attribute`, `unsupported-subscript` | — |
| `unsupported-operator`, `unsupported-comparison` | — |
| `unsupported-loop`, `unsupported-control-flow`, `unsupported-return` | — |
| `unsupported-comprehension`, `unsupported-class`, `unsupported-function` | — |
| `unsupported-statement`, `unsupported-expression`, `unsupported-construct` | fallbacks |

Sidecar-whitelist rejections use a separate family — `bodiless`,
`forbidden-token`, `attribute`, `lambda`, `spec-literal`, `malformed-ghost`,
`non-declaration` — reported through the same `rule` field.

## Concurrency and artifacts

`verify_structured` is safe to call concurrently against a shared `outdir`:
each invocation stages privately and writes its stub atomically. Artifacts
are removed unless `keep_artifacts=True`, in which case the directory is
content-addressed so re-verifying an unchanged file overwrites rather than
accumulates.
