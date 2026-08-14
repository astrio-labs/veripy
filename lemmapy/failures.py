"""The failure taxonomy: the vocabulary a host branches on.

`lemmapy verify --json` reports every outcome as failure records carrying a
`kind`. Those kinds are this toolchain's **public branching surface** — an
embedding host (or a repair agent) decides what to do next by reading them —
so they cannot be an implementation detail of whichever module happened to
raise. Before this module they were split between a substring classifier
over Dafny's prose (`driver.classify_obligation`) and inline literals in
`agentio` / the exam harnesses, with no list of the possible values and no
way for a caller to notice the set changing.

Two rules follow, both enforced by tests:

1. **Every kind the code can emit appears here.** A kind absent from this
   table is a bug, not a new feature — `tests/test_failures.py` scans the
   package for kind literals and fails on an undocumented one.
2. **The set is versioned.** `TAXONOMY_VERSION` travels in every structured
   payload, so a host pinned to one vocabulary can detect a change instead
   of silently mis-routing an unfamiliar kind.

Adding a kind: add it here with what a caller should DO about it, bump
`TAXONOMY_VERSION`, and note the change in docs/AGENT-INTERFACE.md.
"""

from __future__ import annotations

TAXONOMY_VERSION = 1

# Proof obligations the PROVER failed to discharge. Repairable by proof
# additions (the sidecar) without touching source or specs.
PROVER_KINDS: dict[str, str] = {
    "postcondition": "An `#@ ensures` clause was not proved on some return "
                     "path. Strengthen invariants or supply lemmas.",
    "invariant": "A loop invariant failed on entry or was not maintained.",
    "assertion": "An executable `assert` in the source was not proved.",
    "call-precondition": "A callee's `requires` (often a preamble function's "
                         "domain condition, e.g. PySeqMax on a possibly-empty "
                         "sequence) was not established at the call site.",
    "termination": "A `decreases` obligation failed; the prover cannot show "
                   "the loop or recursion terminates.",
    "bounds": "An index was not shown in range (Python's IndexError "
              "condition, modeled by PyIndex).",
    "division": "A divisor was not shown nonzero (Python's "
                "ZeroDivisionError condition).",
    "timeout": "The prover ran out of time or resources on this obligation. "
               "NOT a disproof: the property may still hold.",
}

# The FRONT END refused the input. Not repairable by proof additions —
# the source or the specs must change.
FRONTEND_KINDS: dict[str, str] = {
    "syntax": "The file is not parseable Python (or the spec-comment "
              "tokenizer failed on it).",
    "spec": "A `#@` clause is malformed or names something unknown.",
    "conformance": "The construct is outside the verified fragment; the "
                   "message names what and suggests an alternative.",
    "type": "The basedpyright strict type gate rejected the file.",
}

# The HARNESS or an exam refused, independent of the program's correctness.
HARNESS_KINDS: dict[str, str] = {
    "engine": "A repair/spec engine call failed (unavailable CLI, API error, "
              "wall exceeded). Says nothing about the program.",
    "freeze": "An exam's frozen region was modified — the attempt is "
              "invalid, not wrong.",
}

# Origin genuinely undetermined. `unknown` is NOT a harness kind: it is
# what the prover-message classifier returns for a diagnostic it does not
# recognize, and what a failed run with no parsed diagnostics reports — so
# filing it under "harness" would tell a host to skip proof repair for a
# real, merely-unclassified proof failure. Route it by `region`/`status`
# instead of by group.
UNCLASSIFIED_KINDS: dict[str, str] = {
    "unknown": "The producer could not classify this failure; the raw "
               "message is always attached. Origin is undetermined — use "
               "`status` (a `failed` run means the prover ran) and `region` "
               "(`source` vs `sidecar`) to decide whether proof repair "
               "applies. Do not assume it is harness-only.",
}

FAILURE_KINDS: dict[str, str] = {**PROVER_KINDS, **FRONTEND_KINDS,
                                 **HARNESS_KINDS, **UNCLASSIFIED_KINDS}


def is_known(kind: str) -> bool:
    return kind in FAILURE_KINDS


def describe(kind: str) -> str:
    return FAILURE_KINDS.get(kind, "(not in this taxonomy version)")
