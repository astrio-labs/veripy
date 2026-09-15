# pypa/packaging

Maintained annotated components and checked proof support.

## Components

- [names.py](names.py) with Dafny.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `canonicalize_name` in `src/packaging/utils.py`.
- Old revision `f58537628042c7f29780b9d33f31597e7fc9d664`.
- New revision `3b77a26f5a27473ad3b08194d773f325d018a2d0`.
- Recorded verdict `counterexample-found`.
- Scope Exact Unicode-scalar strings with bool validate, including its keyword-only default; string return or InvalidName class.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects packaging --out build/packaging-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
