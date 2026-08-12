import importlib.util
import sys
from pathlib import Path

import pytest

icontract = pytest.importorskip("icontract")

from lemmapy.backends.runtime.emit import emit_checked
from lemmapy.frontend.extract import parse_source

EXAMPLES = Path(__file__).resolve().parent.parent / "examples"


def _load_checked(source: str, tmp_path: Path, name: str):
    specs = parse_source(source)
    checked = emit_checked(source, specs, src_name=f"{name}.py")
    path = tmp_path / f"{name}_checked.py"
    path.write_text(checked)
    spec = importlib.util.spec_from_file_location(f"{name}_checked", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_clamp_seeded_bug_caught_at_runtime(tmp_path):
    module = _load_checked((EXAMPLES / "clamp.py").read_text(), tmp_path, "clamp")
    assert module.clamp(5, 0, 10) == 5
    assert module.clamp(15, 0, 10) == 10
    with pytest.raises(icontract.errors.ViolationError):
        module.clamp(-5, 0, 10)  # the seeded bug: lower bound ignored


def test_clamp_requires_enforced(tmp_path):
    module = _load_checked((EXAMPLES / "clamp.py").read_text(), tmp_path, "clamp")
    with pytest.raises(icontract.errors.ViolationError):
        module.clamp(0, 10, 5)  # violates `requires lo <= hi`


def test_binary_search_passes_its_contract(tmp_path):
    module = _load_checked(
        (EXAMPLES / "binary_search.py").read_text(), tmp_path, "binary_search"
    )
    xs = [1, 3, 5, 7, 11]
    assert module.binary_search(xs, 7) == 3
    assert module.binary_search(xs, 4) == -1
    assert module.binary_search([], 4) == -1
    with pytest.raises(icontract.errors.ViolationError):
        module.binary_search([3, 1, 2], 1)  # unsorted input violates requires


def test_old_snapshot(tmp_path):
    module = _load_checked((EXAMPLES / "bump.py").read_text(), tmp_path, "bump")
    assert module.bump(41) == 42


BROKEN_BUMP = '''
#@ ensures result == old(x) + 1
def bump(x: int) -> int:
    return x + 2
'''


def test_old_snapshot_catches_wrong_impl(tmp_path):
    module = _load_checked(BROKEN_BUMP, tmp_path, "broken_bump")
    with pytest.raises(icontract.errors.ViolationError):
        module.bump(1)
