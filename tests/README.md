# Test organization

Run the active suite from the repository root with `python -m pytest tests`.
Default pytest discovery is restricted to this directory so it does not traverse
frozen experiments, copied repositories or output archives.

| Folder | Coverage |
| --- | --- |
| `api` | Embedding API and backend registration |
| `cli` | Command behavior and CI workflow controls |
| `frontend` | Parsing, typing, admission and dependency resolution |
| `verification` | Structured results, failure vocabulary and reports |
| `proofs` | Proof repair and hints |
| `dafny` | Dafny encoder and driver |
| `lean` | Lean encoding, proof boundary and execution checks |
| `fragments` | Feature semantics, including checks across multiple backends |
| `compatibility` | Old/new products, domains, outcomes and source binding |
| `guards` | Runtime boundaries |
| `runtime` | Contract emission, CrossHair and differential execution |
| `editor` | Language-server protocol and concurrency |
| `integration` | Repository components and retained proof fixtures |
| `tools` | Research archive integrity and repository hygiene |
| `fixtures` | Shared inputs and lists of maintained examples |

Examples and case-study inputs are shared fixtures. Their source paths are
resolved relative to the repository root. Keep these files when preparing a clean
checkout. Backend tests require installed Dafny or Lean, and typing tests need
basedpyright. Proof integration tests skip explicitly when their required provers are absent.
Use `pytest -rs` to see why each check skipped. A passing subset without provers
is not a full proof run. New backend tests should declare `requires_prover` so
encoding-only tests continue to run without external tools.

`fixtures/difftest.txt` lists sixteen admitted examples for the nightly
differential sweep and guard-import checks. Editor tests share the checked GCD
example and its sidecar. No test depends on the removed benchmark harness or
external benchmark downloads.
