# VeriPy roadmap

The project verifies selected Python components while preserving their executable
bodies, and separately checks scoped compatibility between versions. Broader
Python coverage and stronger automation remain research goals.

## Current baseline

- Ten project folders with maintained source, contracts, checked sidecars and licenses.
- Twenty-five paired proof units and additional scoped Dafny examples.
- Ten reproducible historical comparisons with explicit domains and verdicts.
- Controlled maintenance and upstream preparation results, including failures.
- A subsystem-organized package and test suite, with obsolete benchmark tooling removed.

The [evaluation index](EVALUATION.md) links the evidence. Historical planning,
versioned pilots, frozen implementations and complete experiment records are
preserved in the archive identified by [history.json](../case_studies/history.json).
They are no longer parallel development trees in the active repository.

## Publication and integration

The curated source update was merged into `main` through
[PR #117](https://github.com/astrio-labs/veripy/pull/117). The
[research archive release](RESEARCH-ARCHIVES.md) is published with verified
downloads, checksums and a reproduction guide. Complete private archives and
the manuscript remain local.

Keep generated proof outputs, logs, temporary files and recovery copies outside
the source tree. New research records should receive a new archive version,
preserving earlier successes and failures.

## Research priorities

1. Improve preparation of explicit dependencies and typing environments before
   acquiring another unseen update cohort.
2. Freeze requirements, review authority, both maintenance arms, public libraries,
   budgets and exposure exclusions before new evaluation. Keep all selected failures.
3. Address measured semantic blockers with focused regressions. Rerun relevant
   component proofs and all ten study checks after compiler extensions, preserving
   results in a new output directory rather than adding another source-tree version.
4. Strengthen the translation assurance argument and expand negative controls.
5. Obtain independent manuscript critique and match every claim to its actual scope.

Successful development proofs do not establish autonomous verification, successful
unseen maintenance or a general proof-reuse advantage. Historical negative results
remain negative results after later implementation improvements. The controlled
maintenance study and public-library diagnostic must remain separate analyses.
