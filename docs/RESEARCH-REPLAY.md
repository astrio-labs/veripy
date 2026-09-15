# VeriPy research replay and historical records

Download the [research-2026-09-15 release](https://github.com/astrio-labs/veripy/releases/tag/research-2026-09-15).
The [repository catalog](research-archives/research-2026-09-15.json) records asset
hashes, URLs and completed download verification.

This release supplies research records and executable replay inputs without the
manuscript. It contains successful and unsuccessful trials, rejected requirements
and empty cohorts. Replaying saved results does not collect new model responses
or GPU measurements.

## Assets and integrity

- `veripy-research-replay-2026-09-15.tar.gz` is the supported starting point for replay.
- `veripy-research-history-2026-09-15.tar.gz` preserves selected pre-cleanup case-study history.
- `veripy-research-records-2026-09-15.tar.gz` preserves selected earlier experiment bundles and receipts.
- `MANIFEST.json` identifies the public source commit, original archive hashes and release assets.
- `FILE-INVENTORY.json.gz` hashes every distributed member.
- `SELECTION.json.gz` records every original member and its inclusion, exclusion,
  expansion or relocation. Original archives are retained privately without changes.

Download all release assets into one directory and verify them before extraction.
The verifier uses Python 3.11 or newer and does not extract or execute archive contents.

```sh
shasum -a 256 -c SHA256SUMS
python3 verify_archives.py verify --manifest MANIFEST.json --assets . --contents
mkdir replay
tar -xzf veripy-research-replay-2026-09-15.tar.gz -C replay
cd replay/veripy-supplement
```

On Linux, `sha256sum -c SHA256SUMS` can replace `shasum`. Compare MANIFEST.json
with the catalog from the intended repository revision. Hashes detect changed
bytes and do not authenticate an unknown publisher by themselves.

## Environment

The frozen replay uses Python 3.12.2, Unicode 15.0.0, integer conversion limit
4300, Dafny 4.11.0, Lean 4.33.1 and basedpyright 1.39.10. Linux is the reference
platform. Install .NET 8 and elan, then install the pinned proof toolchains.
Put their executable directories on PATH. Setup requires network access.

```sh
elan toolchain install leanprover/lean4:v4.33.1
dotnet tool install --global dafny --version 4.11.0
python3.12 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-replay.txt
python -m pip install --no-deps -e .
python check_artifact.py
```

The original `requirements-lock.txt` is preserved byte for byte. That artifact
lock requests basedpyright 1.40.1 even though the recorded maintenance protocol
names 1.39.10. The derived `requirements-replay.txt` selects the recorded 1.39.10
gate and, on macOS ARM only, Python Z3 4.15.1.0 to avoid inconsistent wheel platform
tags in newer versions. Other dependency pins are unchanged. These documented
replay adjustments do not rewrite historical environment records or outcomes.

The replay compiler and isolated experiment compilers are frozen historical
versions. They are distinct from the public development commit in MANIFEST.json.
The updated replay MANIFEST.json hashes the research-only view. Its original
artifact manifest is retained under `provenance/`. Compiler reference hashes and
proof inputs are unchanged. Historical receipts and anonymized views retain their
original scope and provenance, rather than becoming newly sealed experiments.

## Reproduction commands

Run these commands from `veripy-supplement` in the pinned environment. Always use
fresh result directories unless explicitly resuming a maintenance replay.

| Check | Command |
| --- | --- |
| Counts from both maintenance arms | `python reproduction/audit_results.py` |
| Short paired proof check | `PYTHONPATH=. python case_studies/lean_hardening/run_matrix.py --out results/paired-smoke --components django-base36 --workers 1 --wall 900` |
| All 25 paired proof units | `PYTHONPATH=. python case_studies/lean_hardening/run_matrix.py --out results/paired --workers 1 --wall 900` |
| Four parser mutation certificates | `PYTHONPATH=. python case_studies/cpython_time_parser_v1/semantics_v1/certify-mutations.py "$PWD/results/mutations"` |
| Ten historical compatibility verdicts | `python reproduction/historical/replay.py --out results/historical` |
| Saved success and unsuccessful candidates | `python reproduction/maintenance/replay.py --out results/maintenance-smoke --cases 000 001 009` |
| All 36 distinct saved bundles | `python reproduction/maintenance/replay.py --out results/maintenance` |

Successful paired replay reports 50 successful backend invocations and unchanged
compiler/input hashes. Mutation replay reports four certified violations.
Historical replay must reproduce four proved-compatible outcomes, one witnessed
counterexample, one inconclusive outcome and four unsupported outcomes. Matching
an expected failure is successful reproduction, not a successful program proof.

The controlled study contains 48 trials across two arms. The post hoc library
diagnostic contains eight separate trials. Thirty-six saved checker bundles and
their mappings cover shared invocations without changing the trial denominators.
Rejected requirements without proof calls remain in the protocol and decision
records. `--resume` accepts only complete, hash-matching maintenance receipts.

For CPU analysis of the retained GPU observations, install NumPy 2.3.2 and SciPy
1.16.3 in an analysis environment and run the following from the supplement root.

```sh
python reproduction/runtime/project/case_studies/repository_driven_v2/sglang-integration/expanded/analyze.py reproduction/runtime/observations --out results/runtime-analysis.json
```

This analyzes all ten matched process pairs. It does not execute another GPU
experiment. New serving measurements require the recorded NVIDIA A10G environment,
model revisions, workloads and schedules. New agent trajectories require fresh
isolated sessions, the recorded model and reasoning policy, and service access.
Credentials and paid infrastructure are not supplied. The retained protocols and
`reproduction/README.md` explain these distinctions and environment requirements.
Later record comparisons use the separate compiler described in
`record-extension/README.md`.

## Historical views and exclusions

Extract history and records into separate empty directories. Their original paths
remain inside the views. Nested archives have been inspected and expanded under
directories ending in `.unpacked`. Source container hashes stay in SELECTION.json.gz.
Original manifests inside those expanded historical bundles describe original
archives, not the filtered public views. Use the release's outer inventory to
verify public bytes. Arbitrary historical commands are not promised to run after
presentation and editorial files have been removed. Use the replay package above.

Manuscript sources, rendered paper pages, typeset presentation files, manuscript
reviews, recovery copies and installed environments are excluded by path policy.
Raw measurements and executable proof inputs under historical `paper/evidence/`
and `paper/listings/` paths remain research records. Requirement-review decisions
remain included. Selection does not filter by proof outcome. Links retain their
metadata in the selection ledger and are not materialized or followed.

Keep the original third-party license notices with their copied sources. This
public release is not an anonymous review package. An archive correction must
receive a new version, retaining earlier published records and their denominators.
