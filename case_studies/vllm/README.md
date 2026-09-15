# vllm-project/vllm

Maintained annotated components and checked proof support.

## Components

- [alignment.py](alignment.py) with Dafny and Lean.
- [optimizer.py](optimizer.py) with Lean.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `_approximate_gcd` in `vllm/v1/core/kv_cache_utils.py`.
- Old revision `74c96922ecb9017f413318c76d1af83aa2ab45a5`.
- New revision `98dff2a81d747d1dba01a47f939f48c3526d4206`.
- Recorded verdict `unsupported`.
- Scope Exact integer lists and exact integer-or-None keyword-only lower_bound including its default; integer result or ValueError class; no cache-manager or GPU claim.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects vllm --out build/vllm-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
