# Repository layout

The package groups implementation code by subsystem. The public embedding API
is `from veripy import api`. Commands are available through `veripy` or
`python -m veripy` after installation.

## Source and supporting material

| Path | Responsibility |
| --- | --- |
| `veripy/api.py` | Stable embedding operations |
| `veripy/cli.py`, `veripy/__main__.py` | Product commands |
| `veripy/compatibility.py` | Old/new component comparison and its CLI |
| `veripy/frontend/` | Parsing, admission, typing, records and dependency closure |
| `veripy/backends/dafny/` | Encoders, semantic models and proof driver |
| `veripy/backends/lean/` | Encoders, checked support, libraries and proof driver |
| `veripy/backends/runtime/` | Runtime contract emission and CrossHair search |
| `veripy/verification/` | Structured verification, diagnostics and reports |
| `veripy/proofs/` | Checked proof repair and hints |
| `veripy/guards/` | Boundary generation and runtime policies |
| `veripy/difftest/` | Compiled-model execution comparisons |
| `veripy/editor/` | Language-server interface |
| `examples/` | Small annotated programs and shared regression inputs |
| `tests/` | Tests grouped by subsystem |
| `case_studies/` | Ten project folders, proof support, provenance and compact evidence |
| `docs/` | User guides, semantics, evaluation and archive catalogs |
| `tools/` | Repository checks and research artifact utilities |

There is no backend-neutral `veripy/ir/` package. Checked sidecars, CrossHair,
Hypothesis, guards, editor integration and proof repair are maintained interfaces.
They have different responsibilities and are not obsolete benchmark machinery.

## Internal import migration

| Previous internal path | Current path |
| --- | --- |
| `veripy.agentio` | `veripy.verification.runner` |
| `veripy.failures` | `veripy.verification.failures` |
| `veripy.report` | `veripy.verification.report` |
| `veripy.repair` | `veripy.proofs.repair` |
| `veripy.hints` | `veripy.proofs.hints` |
| `veripy.lsp` | `veripy.editor.server` |

These were internal paths and do not have forwarding modules. Downstream users
of those internals must update their imports. The stable public API is documented
in [AGENT-INTERFACE.md](AGENT-INTERFACE.md).

`veripy.benchmark`, `veripy.native_repair`, `veripy.native_guard`,
`veripy.proof_edits` and `veripy.proof_diagnostics` were retired along with the
old benchmark and exam harnesses. `veripy benchmark` and `veripy experiment`
are not supported commands. The current `veripy survey` command remains an
untyped source survey, not a proof benchmark.

## Evidence and generated files

The [case-study index](../case_studies/README.md) describes maintained inputs.
Versioned development snapshots, frozen compilers and full experiment logs are
preserved through [research archives](RESEARCH-ARCHIVES.md). Historical paths in
those records name archive members and must not be rewritten as current paths.
Successes, failures and rejected requirements remain in the original cohorts.

The [test guide](../tests/README.md) describes shared fixtures and tool requirements.
Default pytest discovery searches `tests/`. Generated output, temporary files,
caches, installed environments and LaTeX intermediates stay outside Git.
`tools/check_repository_hygiene.py` checks ignore policy and tracked blob sizes.
See [output conventions](OUTPUT-LAYOUT.md).

The public README and workflow asset do not require the manuscript. Private
table generators live under the author's local `paper/tools/`, with their
build entry points in `paper/Makefile`. They are not public product utilities.
A local `paper/` checkout is not needed
for the product commands or the maintained component runners. Historical paper
reproduction uses the separately distributed frozen artifact.
