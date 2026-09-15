# VeriPy case studies

Ten project folders contain the maintained annotated components, proof sidecars,
licenses and the old/new inputs needed for compatibility checks. There are no
versioned study trees or copied verifier implementations here.

| Project | Maintained examples |
| --- | --- |
| [Black](black/README.md) | Range normalization, parsing, mapping and composition |
| [CPython](cpython/README.md) | Calendar arithmetic, date round trips and time parsing |
| [Django](django/README.md) | Base36 conversion and changed-algorithm compatibility |
| [Packaging](packaging/README.md) | Name normalization and historical counterexamples |
| [PyPNG](pypng/README.md) | Inverse filters with explicit buffer alias rules |
| [PyTorch](pytorch/README.md) | Shard overlap, metadata validation and partitioning |
| [SGLang](sglang/README.md) | Allocation planners and alignment helpers |
| [python-stdnum](stdnum/README.md) | Checksum, decimal round trip and validation |
| [vLLM](vllm/README.md) | Padding optimization and alignment helpers |
| [Werkzeug](werkzeug/README.md) | ETag quoting and parsing |

These are component proofs within explicit domains. They do not verify whole
repositories. A compatibility result concerns its selected callable, dependencies,
input domain and modeled observations, not an entire release.

## Check and reproduce

From the repository root, install `python -m pip install -e '.[dev]'` and put
Dafny 4.11.0 and Lean 4.33.1 on `PATH`. The paired cohort uses Python 3.12.2,
Unicode 15.0.0 and the default 4,300-digit integer conversion limit.

```sh
python case_studies/tools/audit.py --encode
python case_studies/tools/run_matrix.py --out build/parity --wall 900
python case_studies/tools/run_compatibility.py --out build/compatibility --wall 60
PYTHONPATH=. python case_studies/tools/certify_parser_mutations.py "$PWD/build/parser-mutations"
```

Use a new output directory for each run. The matrix accepts `--components NAME`
and `--backends dafny lean` for focused checks. All 25 paired units use one Python
source per unit with separate checked backend support. The four additional
Dafny-only modules are CPython `calendar.py`, Packaging `names.py`, PyPNG
`filters.py` and Werkzeug `etags.py`. They are outside the 25-unit paired count.

The matrix uses the public proof API, as the original runner did. Strict typing
is a separate gate. Resolved module initializers and modeled dependency typing
views are explicit in the archived experiment protocol. The proof API alone
does not establish that raw upstream annotations pass basedpyright. Standard
CLI verification performs its typing gate by default.

The compatibility runner compares current verdicts with the recorded ten-boundary
checkpoint and exits nonzero if a verdict changes. Unsupported and inconclusive
results are retained. Later record-product extensions are reported separately in
`evidence/record-compatibility.json`, rather than rewriting the historical table.

## Evidence and provenance

- `components.json` selects the 25 paired inputs and backend choices.
- `compatibility.json` records ten pinned comparisons, domains and input hashes.
- `origins.json` binds retained files to their original archived paths and hashes.
- [Evidence](evidence/README.md) keeps compact results, including unsuccessful trials.
- `history.json` identifies the versioned historical archive and its checksum.
- [Research archives](../docs/RESEARCH-ARCHIVES.md) provides attachment verification,
  frozen reproduction commands and the complete dated catalog.

Large logs, transcripts, frozen compilers, obsolete pilots and repeated checkpoints
were removed from this active tree. They remain together in the historical
archive outside `case_studies`. Original paths inside historical result records
refer to archive members. The dated attachments are prepared locally under
`output/research-archives/2026-09-14/` and should accompany the curated sources
when publishing the full research artifact. They include earlier research
bundles and a byte-identical copy of the frozen submission artifact.

The submitted anonymous artifact retains its original layout. Reproduce the
paper's historical commands inside that artifact, rather than mixing its frozen
measurements with the current compiler. Fresh runs belong under `build/` or
`output/`, both ignored by Git.
