# Evaluation evidence

The [case-study index](../case_studies/README.md) organizes the maintained inputs
by ten real projects. The directory contains source, checked proof support,
licenses, two small runner manifests and compact historical results.

## Functional verification

[components.json](../case_studies/components.json) selects the 25 paired proof
units. Each unit has one annotated Python source and the required Dafny and Lean
support. The six [Linux manifests](../case_studies/evidence/linux) retain the
paper's 50 successful backend invocations. Composed units and repeated helpers
are not independent programs.

Additional Dafny examples cover CPython calendar round trips, Packaging name
normalization, PyPNG inverse filters and Werkzeug ETags. Their original native
integration results are in the [functional portfolio](../case_studies/evidence/functional-portfolio.json).
The complete application integration harnesses, environments and checkpoints
remain in the historical archive. They are separate from the lightweight proof
runner in the current checkout.

## Historical compatibility

[compatibility.json](../case_studies/compatibility.json) records the ten pinned
old/new comparisons, their input hashes, domains and backend choices.
[Historical results](../case_studies/evidence/historical-compatibility.json)
retain proved relations, concrete counterexamples, inconclusive attempts and
unsupported boundaries. Later [record comparisons](../case_studies/evidence/record-compatibility.json)
remain a separate development result.

Run the current compatibility tool against these inputs to check for verdict
drift. A current result does not replace the frozen paper record. Neither a
functional proof nor a selected compatibility proof covers an entire repository.
See [Callable compatibility](CALLABLE-COMPATIBILITY.md).

## Maintenance and integration measurements

The [evidence index](../case_studies/evidence/README.md) links the controlled
maintenance study, library-information diagnostic, unsuccessful calendar search,
review/exposure audit and SGLang GPU analysis. Compact summaries live in
`case_studies/evidence/`. Full inputs, saved candidates and counting utilities
are preserved in the frozen research artifact and experiment-record archives.
They do not require publishing the manuscript source in this repository.

Failed preparation, rejected requirements, admission failures and timeouts remain
part of the research record. Controlled authored changes and exposed development
cases are not successful unseen upstream transfer. CPU guard costs and GPU
measurements have different workloads and must not be pooled.

## Reproduction

Use Python 3.12.2, Dafny 4.11.0 and Lean 4.33.1 for the paired cohort.
Commands, scopes and the separate typing gate are described in
[case_studies/README.md](../case_studies/README.md). Current product tests run with
`python -m pytest tests`; they are engineering checks, not additional case studies.

[history.json](../case_studies/history.json) identifies the complete pre-cleanup
archive by SHA256. The [research archive guide](RESEARCH-ARCHIVES.md) links the
dated catalog and explains how to verify and reproduce the frozen attachments.
They preserve original paths, raw logs, transcripts, frozen compilers, review
decisions and failures. The attachments are prepared locally and must accompany
a full research-artifact publication. Old paths embedded in
historical evidence are archive member names, not current checkout paths.

The submitted anonymous artifact retains its original source layout. Run the
historical reproduction commands inside that artifact using its frozen compiler,
inputs and counting scripts. The [archive guide](RESEARCH-ARCHIVES.md) gives the
commands and attachment status. The optional manuscript's table and figure
builders are authoring utilities, not prerequisites for the public component
runners. They may require evidence files absent from a source-only checkout.

## Selection and interpretation

The ten-project portfolio is a selected supported-fragment evaluation. Source
preparation, domain restrictions and provenance are recorded per project and in
[origins.json](../case_studies/origins.json). Component and composed-unit counts
must not be treated as independent repository samples. The historical discovery
shortlists and proposed selection protocol are retained in the
[documentation archive](RESEARCH-ARCHIVES.md#documentation-history). They are
proposals and screening records, not evidence that every proposed procedure was
executed. In particular, do not infer prospective selection from those documents
or retrospectively relabel development cases as unseen changes.

Verification of mainstream languages and relational products are established
techniques. VeriPy's contribution is the implemented connection between preserved
Python bodies, comment specifications, checked proof support, explicit native
boundaries and scoped compatibility results. The studies do not establish the
first Python verifier, broader coverage than Nagini, a new relational calculus,
or reduced authoring effort relative to direct Dafny or Lean proof development.

The maintenance question is whether an already checked component proof helps
with a later update under the recorded policy. A standalone Dafny hint-completion
score does not include Python admission, dependency preparation, old-proof
construction or version comparison. Conversely, these maintenance results do
not establish superiority on DafnyBench or other proof-generation benchmarks.

Old-proof preparation costs remain part of any lifecycle comparison. Failed
preparation is an end-to-end coverage result, not a disproved requirement and
not a reason to remove a selected case. Conditional completion, library-information
diagnostics and unsuccessful unseen transfer remain distinct findings. The
original author-side comparison notes are preserved in the documentation archive.
