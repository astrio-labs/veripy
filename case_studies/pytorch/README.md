# pytorch/pytorch

Maintained annotated components and checked proof support.

## Components

- [pair.py](pair.py) with Lean.
- [search1d.py](search1d.py) with Dafny and Lean.
- [searchnd.py](searchnd.py) with Dafny and Lean.
- [sharding.py](sharding.py) with Dafny and Lean.
- [tensor.py](tensor.py) with Dafny and Lean.
- [validation.py](validation.py) with Dafny and Lean.

The exact assumptions and properties are the annotations in each source file.
Individual functions and composed units may overlap. These inputs do not establish
whole-project correctness. Full native integration runs remain in the archive.

## Historical compatibility

- Callable `_check_shard_metadata_pair_overlap` in `torch/distributed/_shard/sharding_spec/_internals.py`.
- Old revision `08187d9e0fba026dc8217405802ab5381dc88d90`.
- New revision `2b3ec34829036a65cd9d1398ea72a0167dc37470`.
- Recorded verdict `unsupported`.
- Scope Stable ShardMetadata snapshots with equal ranks and positive integer sizes; exact integer offsets; boolean overlap return. No tensors or distributed execution.

[Old input](compatibility/old.py) and [new input](compatibility/new.py) are retained
because checking compatibility requires both. They are comparison inputs, not
duplicated development checkpoints. Reproduce with a fresh output directory.

```sh
python case_studies/tools/run_compatibility.py --projects pytorch --out build/pytorch-compatibility
```

The recorded verdict is historical. A fresh run uses the current compiler and
reports any changed verdict separately. Input preparation and original sources
are documented in the historical archive referenced by [history.json](../history.json).

## Provenance and license

The revision pair above applies to the selected historical comparison. For all
retained functional inputs, [origins.json](../origins.json) records exact source
hashes and original archive paths. Read [LICENSE](LICENSE) for upstream terms.
VeriPy annotations and evaluation helpers do not change the upstream license.
