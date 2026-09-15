# drj11/pypng

Maintained annotated components and checked proof support.

## Components

- [filters.py](filters.py) with Dafny.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `undo_filter_paeth` in `code/png.py`.
- Old revision `0dfbfda89e59e592a1cb299ee79af3e6e22d72a1`.
- New revision `4632d79ce419299398c2d540f2fe0e09e1480e3f`.
- Recorded verdict `unsupported`.
- Scope Exact equal-length bytearrays, positive integer filter_unit; result may alias scanline, previous distinct from both; None return and all argument buffer poststates.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects pypng --out build/pypng-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
