"""The grammar-contact corpus (examples/contact/) must stay parse-clean.

These 20 files are annotated HumanEval/MBPP tasks — the artifact of the M0
grammar-contact exercise (docs/GRAMMAR-CONTACT.md) and the seed of the M1
end-to-end benchmark corpus.
"""

from pathlib import Path

import pytest

from veripy.frontend.extract import parse_source
from veripy.frontend.typegate import find_basedpyright, run_type_gate

CONTACT = Path(__file__).resolve().parent.parent / "examples" / "contact"
FILES = sorted(CONTACT.glob("*.py"))


def test_contact_corpus_present():
    assert len(FILES) >= 20


@pytest.mark.parametrize("path", FILES, ids=lambda p: p.stem)
def test_specs_parse_clean(path):
    specs = parse_source(path.read_text(), filename=str(path))
    assert specs.functions, "no spec'd functions found"
    assert not specs.errors, [c.error for c in specs.errors]
    assert not specs.orphans
    assert any(fn.by_kind("ensures") for fn in specs.functions), "no ensures clause"


@pytest.mark.skipif(find_basedpyright() is None, reason="basedpyright not installed")
def test_contact_corpus_passes_type_gate():
    result = run_type_gate(FILES)
    assert result.available, result.error
    assert not result.errors, [f"{d.file}:{d.line} {d.message}" for d in result.errors[:5]]
