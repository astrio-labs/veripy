# Case studies

The repository retains components from ten projects. These are scoped verification studies, not proofs of complete applications.

| Project | Area represented |
| --- | --- |
| Black | Formatting-related component behavior |
| CPython | Calendar and parsing components |
| Django | Base-36 conversion and compatibility |
| Packaging | Name handling |
| Werkzeug | HTTP-related string handling |
| python-stdnum | Checksum operations |
| PyPNG | Byte-buffer operations |
| PyTorch | Shard and tensor-related planning components |
| SGLang | Scheduling and planning components |
| vLLM | Alignment and padding components |

Use the [maintained case-study index](../../case_studies/README.md) for exact files, provenance, scopes and runners.

## Replay a historical comparison

From the repository root, with Dafny installed, run

```sh
python case_studies/tools/run_compatibility.py   --projects django --out build/django-compatibility
```

Use a fresh output directory. The runner checks the recorded compatibility verdict against a new run. This does not rerun every experiment or verify all of Django.

For full research records, including unsuccessful trials, use the [archive guide](../RESEARCH-ARCHIVES.md) and [replay instructions](../RESEARCH-REPLAY.md). The [evaluation guide](../EVALUATION.md) distinguishes the claims supported by each cohort.
