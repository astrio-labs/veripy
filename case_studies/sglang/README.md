# sgl-project/sglang

Maintained annotated components and checked proof support.

## Components

- [alignment.py](alignment.py) with Dafny and Lean.
- [live_planner.py](live_planner.py) with Dafny and Lean.
- [planner.py](planner.py) with Dafny and Lean.
- [prefill.py](prefill.py) with automatic backend obligations.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `page_aligned_decode_alloc_lens` in `python/sglang/srt/mem_cache/allocation_sizing.py`.
- Old revision `6916ffc4cba5f6b97a10d7ab07358e8e21b3129e`.
- New revision `0bcd822377da7b5718e674eaf9c870d349424dd1`.
- Recorded verdict `unsupported`.
- Scope Stable nested integer request snapshots; 0<=committed<=allocated, reserve>=0, page_size>0; ordered length lists and total logical increment.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects sglang --out build/sglang-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
