# psf/black

Maintained annotated components and checked proof support.

## Components

- [adjusted.py](adjusted.py) with Dafny and Lean.
- [composition.py](composition.py) with Dafny and Lean.
- [consumer.py](consumer.py) with Dafny and Lean.
- [mapping.py](mapping.py) with Dafny and Lean.
- [normalize.py](normalize.py) with Dafny and Lean.
- [parser.py](parser.py) with Lean.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `is_valid_line_range` in `src/black/ranges.py`.
- Old revision `bdcad23abeb99dee53af0c511b9fd49b0354b28e`.
- New revision `6409f0a51b7bf081ea60a21b21292cfe572fefdc`.
- Recorded verdict `proved-compatible`.
- Scope Exact tuple of two exact integers, all values; boolean return.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects black --out build/black-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
