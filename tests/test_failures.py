"""The failure taxonomy is the host's branching surface, so it must not
drift silently: every `kind` the package can emit has to be published in
lemmapy/failures.py, and the version has to travel with the payload."""

import re
from pathlib import Path

from lemmapy.backends.dafny.driver import _OBLIGATION_KINDS, classify_obligation
from lemmapy.failures import (
    FAILURE_KINDS,
    PROVER_KINDS,
    TAXONOMY_VERSION,
    describe,
    is_known,
)

PACKAGE = Path(__file__).resolve().parent.parent / "lemmapy"
_KIND_LITERAL = re.compile(r'"kind":\s*"([a-z-]+)"')


def test_every_emitted_kind_is_published():
    # Scans the package for `"kind": "..."` literals. A new kind added
    # without publishing it here fails this test — which is the point: an
    # undocumented kind reaching a host is a broken contract, not a
    # feature.
    found: dict[str, set[str]] = {}
    for path in sorted(PACKAGE.rglob("*.py")):
        for kind in _KIND_LITERAL.findall(path.read_text()):
            found.setdefault(kind, set()).add(path.name)
    assert found, "scan found no kind literals — the regex has drifted"
    undocumented = {k: sorted(v) for k, v in found.items() if not is_known(k)}
    assert not undocumented, f"undocumented failure kinds: {undocumented}"


def test_every_classifier_kind_is_a_published_prover_kind():
    # The classifier maps Dafny's prose onto the taxonomy; nothing it can
    # return may be outside PROVER_KINDS (plus "unknown", the documented
    # escape hatch).
    produced = {kind for _, kind in _OBLIGATION_KINDS}
    assert produced <= set(PROVER_KINDS), produced - set(PROVER_KINDS)
    assert classify_obligation("something nobody has seen") == "unknown"
    assert is_known("unknown")


def test_every_published_kind_has_actionable_guidance():
    # A kind is only useful to a caller if it says what to DO; a bare label
    # would push the host back to parsing prose, which is what this
    # replaces.
    for kind, text in FAILURE_KINDS.items():
        assert len(text) > 30, f"{kind}: guidance too thin"
        assert text.endswith("."), f"{kind}: guidance not a sentence"
    assert describe("no-such-kind").startswith("(")


def test_taxonomy_version_travels_with_the_payload(tmp_path):
    from lemmapy.agentio import verify_structured

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n")
    payload = verify_structured(src, tmp_path / "out")
    assert payload["toolchain"]["taxonomy_version"] == TAXONOMY_VERSION
    for failure in payload["failures"]:
        assert is_known(failure["kind"]), failure


def test_prover_and_frontend_kinds_are_disjoint():
    # A kind must have ONE origin: a host distinguishing "the prover could
    # not prove it" from "we refused the input" cannot do that if a label
    # means both.
    from lemmapy.failures import FRONTEND_KINDS, HARNESS_KINDS

    assert not (set(PROVER_KINDS) & set(FRONTEND_KINDS))
    assert not (set(PROVER_KINDS) & set(HARNESS_KINDS))
    assert not (set(FRONTEND_KINDS) & set(HARNESS_KINDS))
    assert len(FAILURE_KINDS) == (len(PROVER_KINDS) + len(FRONTEND_KINDS)
                                 + len(HARNESS_KINDS))


def test_doc_lists_exactly_the_published_kinds():
    # The doc is the host-facing contract, so it must not drift from the
    # module either: a kind published in code but missing from the doc
    # (or vice versa) is the same broken promise as an undocumented kind.
    doc = (Path(__file__).resolve().parent.parent
           / "docs" / "AGENT-INTERFACE.md").read_text()
    documented = set(re.findall(r"^\| `([a-z-]+)` \|", doc, re.M))
    assert documented == set(FAILURE_KINDS), {
        "in code only": sorted(set(FAILURE_KINDS) - documented),
        "in doc only": sorted(documented - set(FAILURE_KINDS)),
    }
    assert f"taxonomy version {TAXONOMY_VERSION}" in doc
