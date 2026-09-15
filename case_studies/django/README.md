# django/django

Maintained annotated components and checked proof support.

## Components

- [base36.py](base36.py) with Dafny and Lean.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `int_to_base36` in `django/utils/http.py`.
- Old revision `5cba975d26d10ff5d85e123fb2084671a009cc9b`.
- New revision `2508be35ca8bc5440b93d3152cd80ee5f8e159e3`.
- Recorded verdict `proved-compatible`.
- Scope Exact integers on Python 3; base36 strings or ValueError class; unreachable six.PY2 branch removed with structural audit.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects django --out build/django-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
