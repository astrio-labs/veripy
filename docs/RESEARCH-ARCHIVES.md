# Versioned research archives

The dated catalog at `docs/research-archives/2026-09-14.json` identifies three
research attachments and a compressed per-file checksum inventory. Their local
release directory is `output/research-archives/2026-09-14/`. This version is
prepared locally and has not been uploaded. The catalog's `release_url` remains
null until the attachments are published.

| Attachment | Contents |
| --- | --- |
| `veripy-case-studies-2026-09-14.tar.gz` | Complete pre-cleanup case-study history, including all 35,648 original files, frozen compilers, protocols, reviews, successes and failures |
| `veripy-paper-artifact-2026-09-14.zip` | Byte-identical copy of the final anonymous review artifact, with pinned environments and isolated reproduction entry points |
| `veripy-experiment-records-2026-09-14.tar.gz` | Earlier research ZIPs and their receipts, paper evidence, and recorded CPU reproduction outputs |
| `veripy-file-inventory-2026-09-14.json.gz` | SHA256 and size for every archived file, with link metadata where present |

Research records retain original paths. The record archive excludes installed
environments and duplicate extracted copies, whose source ZIPs are retained.
It does not select by success status. Early failed attempts and superseded
protocols remain historical evidence, not additional independent trials.
The exact file selection and exclusions are recorded in the catalog.

The later paper-directory cleanup has its own catalog at
`docs/research-archives/paper-2026-09-14.json`. Its local attachment directory is
`output/research-archives/paper-2026-09-14/`. It preserves all 601 original paper
files, including old drafts, reviews, templates and failed builds. Its own
`SHA256SUMS`, per-file inventory and README document verification and recovery.
It supplements the three research attachments above without changing them.

The output-directory consolidation has a separate catalog at
`docs/research-archives/output-2026-09-14.json`. The attachment under
`output/research-archives/output-2026-09-14/` retains 878 previously unarchived
file contents. Its checksummed `RECOVERY.json.gz` maps all 17,540 consolidated
original files to exact members in that archive or the earlier verified archives.
It includes old failed packaging attempts, validation failures and recovery
snapshots. Symlink targets are recorded separately and were not followed.
See [the output layout](OUTPUT-LAYOUT.md) for current working paths.

## Documentation history

The [September 15 documentation catalog](research-archives/docs-2026-09-15.json)
preserves the complete `docs/` tree, root README and citation metadata before
consolidation. Its archive includes the original architecture and scalar
semantics, grammar-contact and coverage surveys, repository discovery records,
selection proposal, contribution notes and one-off Dafny probe. The per-file
inventory preserves all 35 files without filtering by findings or results.

The local attachment directory is
`output/research-archives/docs-2026-09-15/`. It contains the archive, compressed
inventory, manifest, checksum list, verifier and recovery instructions. It is
prepared locally and has not been published. Verify from a development checkout
with Python 3.11 or newer.

```sh
python tools/research/archives.py verify \
  --manifest docs/research-archives/docs-2026-09-15.json \
  --assets output/research-archives/docs-2026-09-15 --contents
```

Extract into a separate empty directory to inspect the original paths. These
notes document earlier designs and screening decisions; they are not current
feature claims or newly executed experiments. The archive's included README
provides exact extraction commands. Earlier research archives remain unchanged.

## Verify before replay

Use Python 3.11 or newer for archive verification. From the directory holding
the release attachments, run the following. On Linux, `sha256sum -c SHA256SUMS`
can replace the macOS `shasum` command.

```sh
shasum -a 256 -c SHA256SUMS
python3 verify_archives.py verify --manifest MANIFEST.json --assets . --contents
```

The first command covers the attachments, catalog, guide and verifier script.
The second checks each attachment's SHA256, then checks every archived member
against the per-file inventory. Missing, modified and extra files fail the
check. It does not extract or execute archived code. Compare `MANIFEST.json`
with the catalog obtained from the intended repository revision. Checksums
detect changed bytes, but do not authenticate an unknown publisher by themselves.

From a development checkout, the equivalent content check is

```sh
python tools/research/archives.py verify \
  --manifest docs/research-archives/2026-09-14.json \
  --assets output/research-archives/2026-09-14 --contents
```

## Reproduce the paper

Start with the frozen paper artifact. Its compiler and original study paths
belong together. The reorganized development compiler is a separate version.
In the attachment directory, extract into a fresh `replay` directory.

```sh
python3 -m zipfile -e veripy-paper-artifact-2026-09-14.zip replay
cd replay/veripy-supplement
python3.12 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-lock.txt
python -m pip install --no-deps -e .
python check_artifact.py
```

The reference CPU environment is Python 3.12.2, Unicode 15.0.0, integer digit
limit 4300, Dafny 4.11.0, Lean 4.33.1 and basedpyright 1.39.10. The packaged
README supplies the .NET 8 and Lean installation commands. Dependencies and
toolchains require network access during setup. `check_artifact.py` checks
every packaged source hash and the Python boundary before replay.

Run these from the extracted `veripy-supplement` root. Use new output paths
unless explicitly resuming a maintenance replay.

| Result | Command or instructions |
| --- | --- |
| Paired component proofs | `PYTHONPATH=. python case_studies/lean_hardening/run_matrix.py --out results/paired --workers 1 --wall 900` |
| Four parser mutation certificates | `PYTHONPATH=. python case_studies/cpython_time_parser_v1/semantics_v1/certify-mutations.py "$PWD/results/mutations"` |
| Ten historical compatibility verdicts | `python reproduction/historical/replay.py --out results/historical` |
| Saved maintenance candidates | `python reproduction/maintenance/replay.py --out results/maintenance` |
| Counts from both maintenance arms | `python reproduction/audit_results.py` |
| Component effort and maintenance tables | `python tools/submission/generate_effort_tables.py` and `python tools/submission/generate_maintenance_metrics.py` |
| Runtime statistics | `python reproduction/runtime/project/case_studies/repository_driven_v2/sglang-integration/expanded/analyze.py reproduction/runtime/observations --out results/runtime-analysis.json` |
| Later record comparisons | Follow `record-extension/README.md` using its separate frozen compiler |

For a short proof smoke check, add `--components django-base36` to the paired
runner. For a short maintenance replay, add `--cases 000`. The full maintenance
replay covers 36 distinct saved bundles and checks expected outcomes, including
retained failures. `--resume` reuses only completed, hash-matching receipts.
The complete controlled experiment still has 48 trials across two arms. Shared
saved bundles, proof invocations and experiment trials have different counts.

The preserved controlled records include 24 joint proofs, 12 typing failures
and 12 exhausted proof budgets. The post hoc library diagnostic stays separate.
Rejected requirements and empty eligible cohorts remain in the record even when
they have no proof invocation. An archive or replay check passing means the
expected records or outcomes matched, not that every program verified.

Statistical replay uses the retained observations with NumPy 2.3.2 and SciPy
1.16.3. It does not collect new model responses or GPU timings. New trajectories
require the recorded policy, model access and fresh isolated sessions. New GPU
measurements require the documented NVIDIA A10G environment and model weights.
The full procedures and limits are in `reproduction/README.md`. Do not relabel
historical results as new experiments or pool incompatible protocols.

## Inspect complete historical records

In the attachment directory, extract the history separately from the frozen
paper artifact. Never overlay one compiler snapshot onto another.

```sh
mkdir history
tar -xzf veripy-case-studies-2026-09-14.tar.gz -C history
mkdir experiment-records
tar -xzf veripy-experiment-records-2026-09-14.tar.gz -C experiment-records
```

The original case-study paths now resolve under `history/`. In particular,
`case_studies/research_evaluation_v2/controlled-01/` contains `maintenance-audit.json`,
`failure-analysis.json`, `FAILURES.md`, protocol records and both arms' transcripts.
Other review and prospective-cohort decisions remain under their original paths.
The record archive retains earlier bundles under `output/research/`, including
pre-fix and development versions. Their own READMEs explain their historical
scope. The original author metadata and paths are retained in the full history,
so the complete history is not an anonymous-review package.

## Git and future releases

Commit the small dated catalog, this guide, archive tooling, canonical case-study
inputs and compact evidence. Store large archives as release attachments or in
versioned research storage. Keep `output/`, `tmp/`, caches, installed environments
and LaTeX intermediates out of Git. CI runs `tools/check_repository_hygiene.py`
to reject tracked ignored files, missing ignore rules and blobs over 10 MiB.
Checksummed inventories and archives remain under ignored `output/` locally.

For a full paper-artifact release, publish all three archives, the inventory,
`MANIFEST.json`, `SHA256SUMS`, the matching archive README and `verify_archives.py`
together. These existing bundles include manuscript sources and nested research
bundles. They are not suitable for a source-only release while the manuscript
remains unpublished. Keep the existing archives unchanged.

### Source-only publication plan

1. Bind a new research release to the reviewed source commit and an immutable
   archive identifier. Keep historical experiment compilers and toolchain locks
   separate from the current development compiler.
2. Inventory the existing archives recursively, including nested ZIPs. Prepare
   a separate research-only bundle containing protocols, requirement decisions,
   inputs, proof support, frozen compilers, logs, transcripts and outcome records.
   Exclude manuscript drafts, reviews of the manuscript and recovery backups.
   Preserve unsuccessful trials, rejected requirements and empty cohorts alongside
   successes. Record every inclusion and exclusion and map retained members to
   their original archive and SHA256. Keep complete originals locally.
3. Add a standalone verifier, per-file inventory, SHA256SUMS, license notices,
   environment locks and reproduction instructions that work without paper files.
   Distinguish rechecking saved outcomes from collecting new model or GPU runs.
   Run integrity checks and representative reproductions from a fresh extraction,
   including an expected unsuccessful outcome.
4. Publish the approved research-only bundle as GitHub Release attachments or in
   versioned research storage. Keep the manuscript and full recovery archives
   private until their publication is separately intended.
5. Download the published files, verify their checksums and inventory, and only
   then add the real release URL to the new catalog. Leave earlier unpublished
   catalogs marked as local. A local path is not a public availability claim.

Archive identifiers are immutable. For a correction, create a new dated identifier
and explain which earlier version it supersedes. Preserve the previous archive,
its failures and denominators. `tools/research/archives.py package --help`
documents the packaging interface. It refuses existing output paths and catalog
versions, verifies the complete original case-study file list, and binds selected
record files by hash. It never filters by experiment outcome.
