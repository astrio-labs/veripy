# arthurdejong/python-stdnum

Maintained annotated components and checked proof support.

## Components

- [checksum.py](checksum.py) with Dafny and Lean.
- [roundtrip.py](roundtrip.py) with Dafny and Lean.
- [validation.py](validation.py) with Lean.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `checksum` in `stdnum/luhn.py`.
- Old revision `d66998e6c6af5852b2761060c12c1a48a1c167ec`.
- New revision `52d316200c347b4f3d2b61a77ce746f3d28a3815`.
- Recorded verdict `inconclusive`.
- Scope Exact Unicode-scalar strings number and alphabet with len(alphabet)>1, including omitted default alphabet; integer return or exception class.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects stdnum --out build/stdnum-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
