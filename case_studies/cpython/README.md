# python/cpython

Maintained annotated components and checked proof support.

## Components

- [calendar.py](calendar.py) with Dafny.
- [calendar_helpers.py](calendar_helpers.py) with automatic backend obligations.
- [rounding.py](rounding.py) with Dafny and Lean.
- [time_parser.py](time_parser.py) with Lean.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `_days_before_year` in `Lib/_pydatetime.py`.
- Old revision `60403a5409ff2c3f3b07dd2ca91a7a3e096839c7`.
- New revision `ebf955df7a89ed0c7968f79faec1de49f61ed7cb`.
- Recorded verdict `proved-compatible`.
- Scope Exact positive integers year >= 1; integer return. Other calendar helpers and round trips are outside this relational verdict.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects cpython --out build/cpython-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
