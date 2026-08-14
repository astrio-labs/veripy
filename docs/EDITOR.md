# The editor surface

`lemmapy lsp` speaks Language Server Protocol over stdio. It has no
dependencies beyond the standard library, so an editor can launch it from
the same virtualenv as the rest of the toolchain.

It runs at **two speeds**, because conformance and proof cost three orders
of magnitude apart:

| | trigger | cost | mechanism |
|---|---|---|---|
| **Conformance** | automatic, every keystroke | milliseconds | spec parse + encoder dry-run |
| **Proof** | explicit request only | seconds to minutes | Dafny |

Nothing on the keystroke path ever launches the prover. That is the whole
design: an editor that pauses for the SMT solver is an editor people turn
off.

## Standard methods

`initialize`, `shutdown`, `exit`, and `textDocument/{didOpen,didChange,didSave,didClose}`
(full-text sync). Diagnostics arrive as `textDocument/publishDiagnostics`.

An unknown request gets a proper `-32601 MethodNotFound` rather than
silence, so a client never hangs on an id that will not be answered.

## `lemmapy/functionStatus`

Per-function state for code lenses and gutter icons.

```jsonc
// -> request
{"textDocument": {"uri": "file:///m.py"}}
// <- result
{"functions": [{"name": "bump", "line": 3,
                "markedVerified": true,        // the `#@ verified` marker
                "status": "conformant",        // fragment conformance
                "proof": "verified"}],         // the prover's verdict
 "proofStatus": "ok"}                          // whole-module, or null
```

`markedVerified` is **intent** and `proof` is **state**; a lens that shows
one as the other is the mistake this split exists to prevent. A function
marked `#@ verified` whose `proof` is `failed` is exactly the case worth
drawing attention to.

## `lemmapy/verify`

Runs the real prover over the current buffer.

```jsonc
// -> request
{"textDocument": {"uri": "file:///m.py"}, "timeLimit": 20}
// <- result
{"status": "failed",                    // the structured payload's status
 "toolchain": {"preamble_version": "0.5", "dafny_version": "4.11.0",
               "taxonomy_version": 1},
 "functions": [{"name": "bump", "proof": "failed"}],
 "diagnostics": [ /* LSP diagnostics, also republished */ ],
 "error": null}
```

- Bind it to a command or a save hook — never to `didChange`.
- It answers from a **worker thread**, so the server keeps serving
  completions, status requests and diagnostics while Dafny thinks. The
  reply may therefore arrive after replies to later requests, which is
  legal LSP.
- `timeLimit` is clamped to 1–300 seconds. A client typo cannot park a
  prover for the session.
- **The newest request for a document wins.** A request still in flight
  when a later one arrives for the same document is *superseded*: it is
  answered with `-32801 ContentModified` and never writes the proof cache.
  Answered, because a client blocked on an id nobody replies to waits
  forever; superseded, because it was decided by completion order what the
  cache holds — a stale timeout could replace a newer success, and a
  result for text the user has since changed is cached and then discarded
  as stale, taking the current verdict with it. A client that gets
  `-32801` should use the reply to the newer request, not re-ask.
- **One prover at a time.** Requests queue; nothing upstream throttles
  them, and a save hook or a held-down keybinding would otherwise mean one
  Dafny process per event. A burst on one document collapses to a single
  run, since everything but the newest is superseded at the head of the
  queue, before a process is started.
- The buffer does not need to be saved. It is staged to a temp directory
  under its own stem, together with the on-disk `<stem>.proofs.dfy` if one
  exists — without that, every `#@ proof` clause would come back as
  `unknown lemma`, a rejection manufactured by the staging rather than a
  fact about the code. A sidecar that exists but cannot be copied is a
  `tool-error` naming it, never that manufactured rejection.
- `exit` waits (bounded) for an in-flight proof, so its reply is delivered
  rather than dropped.

## Proof results expire when the buffer changes

A proof result is pinned to the SHA-256 of the text that produced it. On
the next edit it is **discarded** — not greyed out, not re-anchored:

- its diagnostics stop being republished, and
- `functionStatus` reports `proof: "unknown"` with `proofStatus: null`.

A proof diagnostic sitting on a line the user has since rewritten is worse
than no diagnostic. `unknown` covers both "never proved" and "proved, then
edited", which from a lens's point of view are the same statement: nothing
currently backs a claim about this code.

## What `proof` can say

| value | meaning |
|---|---|
| `verified` | the **whole module** verified (`status: "ok"`) |
| `failed` | a failure is attributed to this function |
| `unknown` | no current result, or the run failed elsewhere |

`verified` is only ever reached through a wholly `ok` module. In a failed
run a function with no failure of its own is `unknown`, never `verified`:
a sidecar lemma that did not verify is assumed by everything that invokes
it, and a function calling a peer whose postcondition failed is correct
only modulo a contract nothing discharges. Either would otherwise render
as a green check beside code that has not been proven.

A `tool-error` (no prover on `PATH`, unreadable sidecar, a crash) is
reported as one **information**-severity diagnostic and claims nothing
about the code — it is not a verdict.

Conformance and spec rejections (`encode-error`, `spec-error`) produce
**no** diagnostics from this lane. The instant lane already published
them, line-precise, on the last keystroke — and it reports a superset,
since it encodes without the sidecar. Every function comes back
`unknown`: the prover was never reached.

## Not yet wired

The type gate (basedpyright) is still a batch tool (`lemmapy check
--types`), and there are no hovers or code actions. `lemmapy verify
--report` remains the authority for the full report, including assumptions
A1–A7.
