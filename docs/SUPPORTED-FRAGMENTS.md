# Supported fragments and evaluated boundaries

Maintained documentation checked September 15, 2026. Historical results retain
their original dates and compiler identities. “Both” means the linked scoped inputs
have retained proofs in Dafny and Lean; it does not imply arbitrary Python using
the same syntax. The [25-unit inventory](../case_studies/components.json)
records exact sources and proof support. The retained Linux evidence records
25 paired units and 50 successful backend invocations. Fresh execution is
recorded separately.

| Fragment | Dafny / Lean evidence | Restrictions and runnable example | Admission/semantic controls |
|---|---|---|---|
| Integer/Boolean arithmetic, branches, loops | Both | Exact builtin types, mathematical integers; explicit contracts and loop invariants where needed. [Scalar examples](../case_studies/components.json) | [conformance](../tests/frontend/test_conformance.py), [imperative](../tests/lean/test_lean_imperative.py) |
| Owned lists, indexing, append, selected indexed multiplication | Both | Ownership and alias restrictions; selected operation forms, not general mutable object graphs. [Parser](../case_studies/cpython/time_parser.py) | [imperative](../tests/lean/test_lean_imperative.py) |
| Strings, slices, split, decimal conversion | Both for selected forms | Python 3.12.2, Unicode 15 and digit limit 4300; checked conversion errors. [Black parser](../case_studies/black/parser.py) | [decimal assignment](../tests/fragments/test_direct_decimal_assignment.py), [translation](../tests/lean/test_lean_translation_audit.py) |
| Tuple generators, reversed, stepped slices, sum/divmod, alphabet lookup | Both for checksum forms | Statically admitted sequence patterns. Exact Luhn algebra is decimal-only; arbitrary alphabets have weaker contracts. [checksum](../case_studies/stdnum/checksum.py) | [sequences](../tests/lean/test_lean_checksum_sequences.py) |
| Helper calls and lazy map consumption | Both for selected parser closure | Statically resolved bodies, contracts and evaluation order; not arbitrary higher-order Python. [full parser](../case_studies/cpython/time_parser.py) | [imperative](../tests/lean/test_lean_imperative.py), [dependency extraction](../tests/frontend/test_dependency_closure.py) |
| Modeled exceptions and custom hierarchy | Both for validation closure | Distinct class tags, restricted single-handler try regions; messages/identity/tracebacks/resource errors excluded. [precise boundary](../case_studies/stdnum/README.md) | [custom errors](../tests/lean/test_lean_custom_exceptions.py) |
| Frozen record snapshots | Both for selected SGLang/PyTorch functional units | Explicit record fields and snapshot assumptions; matching closed schemas now support Dafny old/new value-snapshot products; Lean functional checks remain separate. See [record development/reuse](../case_studies/evidence/README.md). [paired inventory](../case_studies/components.json) | [conformance](../tests/frontend/test_conformance.py) |
| Regex/Unicode normalization extensions | Scoped Dafny evidence; expanded closure Lean parity unestablished | Registered patterns and pinned models; not general regex. [extension scopes](../case_studies/evidence/README.md) | [conformance](../tests/frontend/test_conformance.py) |
| ASCII percent decoding and mandatory charset captures | Scoped Dafny definitions and composed proof; Lean parity unestablished | Exact `urllib.parse.unquote` boundary, four replacement codecs, ASCII call precondition and transitive dependency guards. [scope and evidence](../case_studies/evidence/README.md) | [decoder tests](../tests/fragments/test_percent_decoding.py), [capture tests](../tests/fragments/test_header_charsets.py) |
| Byte-buffer mutation and alias rules | Scoped Dafny evidence; Lean parity unestablished | PyPNG filters with explicit buffer boundaries; historical buffer product unsupported. [extensions](../case_studies/evidence/README.md) | [buffer tests](../tests/fragments/test_buffer_backend.py) |
| Constants, defaults, keyword-only parameters | Scoped dependency/comparison support | Matching admitted immutable defaults; optional and changed-default relational restrictions remain. Automatic extraction does not invent specifications. [extractor study](../case_studies/evidence/README.md) | [dependency tests](../tests/frontend/test_dependency_closure.py) |

Reproduce a named unit from the repository root with a fresh output directory.
Both backends are the default. Replace `django-base36` with another component
identifier from the inventory.

```sh
python case_studies/tools/run_matrix.py --out build/paired-django \
  --components django-base36 --wall 900
```

The pinned Linux workflow exercises every registered unit and retains artifacts.

Translation correctness is not a mechanized end-to-end Python theorem. Lean
kernel checks, allowed-axiom audits, rejection tests, differential execution and
mutation witnesses provide distinct evidence; none substitutes for the others.
