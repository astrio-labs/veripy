# pallets/werkzeug

Maintained annotated components and checked proof support.

## Components

- [etags.py](etags.py) with Dafny.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `quote_etag` in `src/werkzeug/http.py`.
- Old revision `6389612fd1ee1bd93579eed5026e8fd471d04abd`.
- New revision `c1a26b45fb06d5e086b4d6be820c3302f588d815`.
- Recorded verdict `proved-compatible`.
- Scope Exact Unicode-scalar strings and exact bool weak, including omitted weak=False; string return or ValueError class. Parser and ETags object state excluded.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects werkzeug --out build/werkzeug-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
