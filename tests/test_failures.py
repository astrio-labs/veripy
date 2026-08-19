"""The failure taxonomy is the host's branching surface, so it must not
drift silently: every `kind` the package can emit has to be published in
veripy/failures.py, and the version has to travel with the payload."""

import re
from pathlib import Path

from veripy.backends.dafny.driver import _OBLIGATION_KINDS, classify_obligation
from veripy.failures import (
    FAILURE_KINDS,
    PROVER_KINDS,
    TAXONOMY_VERSION,
    describe,
    is_known,
)

PACKAGE = Path(__file__).resolve().parent.parent / "veripy"
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
    # Sidecar resolution errors are their own kind: the proof was never
    # attempted, so "strengthen the proof" is the wrong instruction. All 15
    # unclassified records in the first n=6 live run were of this shape.
    for msg in ("unresolved identifier: PyMaxSeq",
                "wrong number of arguments (got 1, but function 'PyMax' "
                "expects 2: (a: int, b: int))",
                "incorrect argument type for function parameter 'a' "
                "(expected int, found seq<int>)"):
        assert classify_obligation(msg) == "resolution", msg
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
    from veripy.agentio import verify_structured

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
    import itertools

    from veripy.failures import (FRONTEND_KINDS, HARNESS_KINDS,
                                  UNCLASSIFIED_KINDS)

    groups = [PROVER_KINDS, FRONTEND_KINDS, HARNESS_KINDS, UNCLASSIFIED_KINDS]
    for a, b in itertools.combinations(groups, 2):
        assert not (set(a) & set(b)), (sorted(a), sorted(b))
    assert len(FAILURE_KINDS) == sum(len(g) for g in groups)
    # `unknown` is its own origin, NOT harness: the prover-message
    # classifier returns it, so filing it under harness would tell a host
    # to skip proof repair on a real unclassified proof failure.
    assert "unknown" in UNCLASSIFIED_KINDS and "unknown" not in HARNESS_KINDS
    assert classify_obligation("no rule matches this") == "unknown"


def test_every_status_carries_provenance(tmp_path, monkeypatch):
    # The doc promises `toolchain` on EVERY payload. The CLI's gate-error
    # path built its own dict and omitted it, so hosts reading the
    # documented field would KeyError on a reachable outcome.
    import json

    from veripy.agentio import new_payload
    from veripy.cli import main
    from veripy.frontend.typegate import find_basedpyright

    skeleton = new_payload("x.py")
    assert set(skeleton["toolchain"]) == {"preamble_version", "dafny_version",
                                         "taxonomy_version"}

    if find_basedpyright() is None:
        return
    (tmp_path / "pyrightconfig.json").write_text('{"typeCheckingMode": "strict"}\n')
    (tmp_path / "m.py").write_text(
        "#@ ensures result >= 0 or result < 0\ndef f(x):\n    return x\n")
    monkeypatch.chdir(tmp_path)
    out = tmp_path / "failures.json"
    assert main(["verify", "m.py", "-o", str(tmp_path / "o"),
                 "--json", str(out)]) == 2
    payloads = json.loads(out.read_text())
    assert payloads[0]["status"] == "gate-error"
    assert payloads[0]["toolchain"]["taxonomy_version"] == TAXONOMY_VERSION
    for f in payloads[0]["failures"]:
        assert is_known(f["kind"])


def test_doc_lists_exactly_the_published_kinds():
    # The doc is the host-facing contract, so it must not drift from the
    # module either: a kind published in code but missing from the doc
    # (or vice versa) is the same broken promise as an undocumented kind.
    doc = (Path(__file__).resolve().parent.parent
           / "docs" / "AGENT-INTERFACE.md").read_text()
    # Scope to the taxonomy section: the document also tabulates rejection
    # `rule` ids, which are a DIFFERENT namespace in the same table shape,
    # and scanning the whole file would conflate the two.
    section = doc.split("## The failure taxonomy", 1)[1].split("\n## ", 1)[0]
    documented = set(re.findall(r"^\| `([a-z-]+)` \|", section, re.M))
    assert documented == set(FAILURE_KINDS), {
        "in code only": sorted(set(FAILURE_KINDS) - documented),
        "in doc only": sorted(documented - set(FAILURE_KINDS)),
    }
    assert f"taxonomy version {TAXONOMY_VERSION}" in doc


def test_unattributable_failure_reports_null_region(tmp_path, monkeypatch):
    # A failed prover run with no parseable diagnostics still owes the
    # caller a failure record — but it must not FABRICATE where the failure
    # lives. The contract routes `unknown` by `region`, so a hardcoded
    # "source" would send a repair agent after the wrong file.
    import veripy.agentio as agentio_mod
    from veripy.backends.base import get_backend
    from veripy.backends.dafny.driver import VerifyResult

    # Patch the backend seam (what the pipeline actually calls), not the
    # driver function agentio once imported directly.
    monkeypatch.setattr(
        get_backend("dafny"), "verify_artifact",
        lambda *a, **k: VerifyResult(ok=False, diagnostics=[],
                                     summary="finished with 0 verified, 1 error",
                                     raw="opaque prover output"))
    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n")
    payload = agentio_mod.verify_structured(src, tmp_path / "out")

    assert payload["status"] == "failed"
    assert len(payload["failures"]) == 1, "a failed run must not be empty"
    failure = payload["failures"][0]
    assert failure["kind"] == "unknown"
    assert failure["region"] is None, "region must not be fabricated"
    assert failure["py_line"] is None and failure["function"] is None
    assert failure["message"]  # the raw prover output is always attached
