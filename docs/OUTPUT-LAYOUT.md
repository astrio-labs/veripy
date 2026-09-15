# Generated output conventions

`build/`, `output/`, `tmp/`, caches and installed environments are ignored by Git.
Choose a fresh output directory for new proof or comparison runs. Keep recorded
historical results separate from current compiler runs.

| Path convention | Purpose |
| --- | --- |
| `build/<activity>/` | Disposable development proof and test artifacts |
| `output/paper/` | Manuscript builds when the optional local paper source is present |
| `output/research-archives/<version>/` | Immutable research attachments, inventories and checksums |
| `output/validation/<date>/<activity>/` | Validation receipts, including failed attempts |
| `output/submission-<identifier>/` | Frozen submission snapshots, if retained locally |
| `.venv/` | Local development environment |

## Portable development setup

From the repository root, with Python 3.11 or newer installed.

```sh
python -m venv .venv
source .venv/bin/activate
python -m pip install -e '.[dev]'
python -m pytest tests
```

Use the pinned Python and external toolchains in the
[case-study guide](../case_studies/README.md) for comparable proof runs. Installing
the Python package alone does not install Dafny or Lean. Existing local virtual
environments can stay at their original paths; do not assume that moving one
preserves its launchers.

## Research archives and recovery

Store large raw records as versioned attachments with per-file checksums and
reproduction instructions. Retain compact, relevant receipts with each activity,
and publish maintained historical summaries under `case_studies/evidence/`.
A local output directory is not a public download location.

The September 14 output-history archive retains the recovery map for earlier
working paths and duplicate extractions. The September 15 documentation archive
preserves the detailed cleanup accounting that previously appeared in this guide.
Both catalogs are linked from [research archives](RESEARCH-ARCHIVES.md).
Do not change embedded historical paths or hashes to match a new working layout.
