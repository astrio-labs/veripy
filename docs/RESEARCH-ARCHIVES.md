# Versioned research archives

The public [research-2026-09-15 release](https://github.com/astrio-labs/veripy/releases/tag/research-2026-09-15)
contains research records, frozen compilers and executable replay inputs. Start
with the [replay guide](RESEARCH-REPLAY.md). The manuscript and complete private
recovery archives are not included.

The [release catalog](research-archives/research-2026-09-15.json) records actual
download URLs, SHA256 hashes, publication time and download verification. All
eleven attachments were downloaded after publication and checked against their
hashes. The inventory verified all 95,523 distributed files. The manifest was
also downloaded successfully without authentication.

| Archive | Contents | Compressed size |
| --- | --- | --- |
| `veripy-research-replay-2026-09-15.tar.gz` | Supported replay package with frozen proof inputs, saved maintenance candidates, counting scripts and environment locks | 18 MiB |
| `veripy-research-history-2026-09-15.tar.gz` | Pre-cleanup case-study history, protocols, requirement reviews, proof support and logs | 119 MiB |
| `veripy-research-records-2026-09-15.tar.gz` | Earlier experiment bundles, transcripts, receipts and retained observations | 170 MiB |

The other attachments are `MANIFEST.json`, `FILE-INVENTORY.json.gz`,
`SELECTION.json.gz`, `SHA256SUMS`, `VALIDATION.json`, `README.md`,
`verify_archives.py` and `public_release.py`.

## Verify and replay

Download all attachments into one directory. With Python 3.11 or newer, run

```sh
shasum -a 256 -c SHA256SUMS
python3 verify_archives.py verify --manifest MANIFEST.json --assets . --contents
```

On Linux, use `sha256sum -c SHA256SUMS`. Verification does not extract or execute
archived code. Compare the manifest hash with the repository catalog. The catalog
adds publication metadata and URLs to the manifest's content records.

The equivalent check from this checkout is

```sh
python tools/research/archives.py verify \
  --manifest docs/research-archives/research-2026-09-15.json \
  --assets /path/to/downloaded-assets --contents
```

Follow [RESEARCH-REPLAY.md](RESEARCH-REPLAY.md) for extraction, pinned toolchains
and reproduction commands. It documents the derived replay lock and the original
artifact lock discrepancy. Historical compiler snapshots have their own hashes
and must be used with their matching inputs. The release tag binds the validated
public development source at `3557039eaafa8d039b680c403873259d362a8baf`, which
is a separate compiler revision.

Fresh extraction checks reproduced the recorded counts from both maintenance
arms, both backend proofs for Django base36, all ten historical verdicts and
saved maintenance candidates 000, 001 and 009. Those candidates include expected
proof and typing failures. `VALIDATION.json` records the exact scope. The release
check did not rerun every component or saved bundle and made no new model calls
or GPU measurements.

## Selection and historical scope

Successful and unsuccessful trials, rejected requirements and empty cohorts
remain in the public records. Selection does not filter by outcome. The builder
recursively inspected 98,451 original archive members, including 95 nested
containers. `SELECTION.json.gz` records each inclusion, exclusion, expansion,
relocation and original content hash. Links are represented as metadata and
were not followed or materialized.

Manuscript sources, typeset presentation files, manuscript reviews, recovery
copies and installed environments are excluded by path. Raw measurements and
executable proof inputs under historical `paper/evidence/` and `paper/listings/`
paths remain research data. Requirement-review decisions remain included.

Expanded nested bundles use directories ending in `.unpacked`. Their internal
manifests describe the original historical bundles. The release's outer
inventory describes the distributed view. Historical paths in evidence records
are archive member names, not paths in the maintained checkout. Use the supported
replay package for runnable commands. Earlier attempts and overlapping snapshots
are provenance, not additional independent experiments.

## Complete private archives

Original archives remain unchanged locally. Their catalogs retain their local
publication status and null release URLs. The public release is a derived view,
not a publication of these complete bundles.

| Catalog | Preserved material |
| --- | --- |
| [2026-09-14](research-archives/2026-09-14.json) | Complete case-study history, byte-identical submission artifact and earlier experiment records |
| [paper-2026-09-14](research-archives/paper-2026-09-14.json) | All 601 original paper files, including drafts, reviews, templates and failed builds |
| [output-2026-09-14](research-archives/output-2026-09-14.json) | 878 additional file contents and a recovery map for 17,540 consolidated original files |
| [docs-2026-09-15](research-archives/docs-2026-09-15.json) | Documentation before consolidation, including all 35 original files |

These local bundles are under `output/research-archives/<version>/`. Each has its
own inventory, checksums and recovery instructions. See the
[output layout](OUTPUT-LAYOUT.md) for working paths. Do not upload a private
bundle in place of the research-only release.

### Documentation history

The [documentation catalog](research-archives/docs-2026-09-15.json) preserves the
earlier architecture and semantics, grammar and coverage surveys, repository
discovery records, selection proposal, contribution notes and one-off Dafny
probe. They are historical designs and findings, not current feature claims.
Verify the local documentation archive with

```sh
python tools/research/archives.py verify \
  --manifest docs/research-archives/docs-2026-09-15.json \
  --assets output/research-archives/docs-2026-09-15 --contents
```

## Future releases

Commit small catalogs, archive tooling, canonical case-study inputs and compact
evidence. Store large records as release attachments. Keep `output/`, `tmp/`,
caches, installed environments and LaTeX intermediates out of Git. CI checks
for tracked ignored files and blobs larger than 10 MiB.

`tools/research/public_release.py --help` describes the research-view builder.
Building a view requires the complete local originals. Verifying or replaying
the public release does not. The builder refuses an existing output directory,
checks original archive hashes, inspects nested containers and emits a selection
ledger and per-file inventory. The attached builder and verifier preserve the
packaging implementation used for this release.

Use a new dated identifier for corrections. Preserve earlier published bytes,
failures and denominators. Before publishing, verify a fresh extraction and
replay successful and unsuccessful outcomes. After publication, download and
verify the attachments before recording their URLs in a new catalog.
