# VeriPy documentation

Start with the [project README](../README.md) for installation, the verification
workflow and a runnable comparison. These guides describe the maintained source
tree. Research results retain their own compiler, environment and input bindings.

## Using VeriPy

| Guide | Read it for |
| --- | --- |
| [Specification language](SPEC-GRAMMAR.md) | Contracts, invariants, proof hooks and runtime versus static meaning |
| [Supported fragments](SUPPORTED-FRAGMENTS.md) | Backend-specific scope and evaluated inputs |
| [Dafny backends](DAFNY.md) | Setup, backend selection, checked support and runtime boundaries |
| [Lean backend](LEAN.md) | Setup, checked support, execution model and axiom policy |
| [Callable compatibility](CALLABLE-COMPATIBILITY.md) | Comparing versions, relation lemmas and verdicts |
| [Embedding API](AGENT-INTERFACE.md) | Structured outcomes, proof repair and host integration |
| [Editor integration](EDITOR.md) | Diagnostics, verification requests and stale-result handling |

## Understanding the implementation

| Guide | Read it for |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Admission, translation, proof backends and execution checks |
| [Semantics](SEMANTICS.md) | Values, evaluation order, dependencies, exceptions, records and buffers |
| [Assurance argument](ASSURANCE-ARGUMENT.md) | Conditional guarantees and remaining trust |
| [Repository layout](REPOSITORY-LAYOUT.md) | Package structure and internal import migration |
| [Output conventions](OUTPUT-LAYOUT.md) | Portable setup and generated artifact locations |
| [Tests](../tests/README.md) | Subsystem suites, fixtures and external tool requirements |

## Research evidence

- [Case studies](../case_studies/README.md) identifies the ten projects and maintained runners.
- [Evaluation](EVALUATION.md) separates functional, compatibility, integration and maintenance evidence.
- [Research archives](RESEARCH-ARCHIVES.md) provides catalogs, checksums, reproduction and availability status.
- [Roadmap](ROADMAP.md) records remaining engineering and research priorities.

Earlier surveys, selection proposals and design notes are preserved in the
[documentation history](RESEARCH-ARCHIVES.md#documentation-history). They are
not parallel current guides. The workflow image and its standalone vector source
have their own [provenance note](assets/README.md).
