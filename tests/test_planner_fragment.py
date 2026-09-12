"""Record snapshots, enumerate prefixes and owned scalar list updates."""
import ast
from pathlib import Path

import pytest

from veripy.api import verify
from veripy.backends.dafny.encoder import encode_module, EncodeError
from veripy.backends.dafny.driver import find_dafny
from veripy.frontend.extract import parse_source
from veripy.difftest.harness import difftest_file, _load_original_module
from veripy.guards.emitter import emit_guarded
from veripy.guards.runtime import TypeGuardError, guard_value


RECORDS = '''from dataclasses import dataclass
@dataclass(frozen=True)
class KV:
    allocated: int
@dataclass(frozen=True)
class Request:
    kv: KV

'''
COLLECT = '''#@ ensures len(result) == len(reqs)
#@ ensures forall j in range(len(reqs)) :: result[j] == reqs[j].kv.allocated
def collect(reqs: list[Request]) -> list[int]:
    out = [0] * len(reqs)
    for i, r in enumerate(reqs):
        #@ invariant len(out) == len(reqs)
        #@ invariant forall j in range(i) :: out[j] == reqs[j].kv.allocated
        out[i] = r.kv.allocated
    return out
'''


def encode(source):
    return encode_module(source, parse_source(source), "records.py")


@pytest.mark.parametrize("source", [
    RECORDS.replace("frozen=True", "frozen=False") + COLLECT,
    RECORDS.replace("class KV:", "class KV(object):") + COLLECT,
    RECORDS.replace("allocated: int", "allocated: int = 0") + COLLECT,
    RECORDS.replace("allocated: int", "allocated: list[int]") + COLLECT,
    RECORDS.replace("allocated: int", "allocated: Request") + COLLECT,
    RECORDS.replace("    allocated: int", "    allocated: int\n    def evil(self):\n        return 0") + COLLECT,
    RECORDS + COLLECT + "KV = int\n",
    RECORDS + COLLECT + "def unused(x: effect()):\n    return x\n",
    RECORDS + COLLECT.replace("        out[i] = r.kv.allocated", "        r.kv.allocated = 0"),
    RECORDS + COLLECT.replace("        out[i] = r.kv.allocated", "        out[i] = r.kv.missing"),
    RECORDS + COLLECT.replace("enumerate(reqs)", "enumerate(reqs, 1)"),
    RECORDS + COLLECT.replace("#@ invariant len(out) == len(reqs)", "#@ invariant r.kv.allocated >= 0"),
    RECORDS + COLLECT.replace("out[i] =", "out[(i := 0)] ="),
])
def test_unsupported_record_and_iteration_semantics_rejected(source):
    with pytest.raises(EncodeError):
        encode(source)


@pytest.mark.parametrize("body", [
    "xs[0] = 1\n    return xs",
    "local = [0]\n    alias = local\n    local[0] = 1\n    return alias",
    "local = [0]\n    box = (local, 0)\n    local[0] = 1\n    return box[0]",
    "local = [0]\n    box = [local]\n    local[0] = 1\n    return box[0]",
    "local = [0]\n    for v in local:\n        local[0] = v\n    return local",
    "local = [[0]] * 2\n    return local[0]",
])
def test_mutation_and_repetition_aliases_fail_closed(body):
    with pytest.raises(EncodeError):
        encode("#@ ensures True\ndef f(xs: list[int]) -> list[int]:\n    " + body + "\n")


@pytest.mark.skipif(find_dafny() is None, reason="Dafny required")
def test_record_loop_verifies_and_executes(tmp_path):
    path = tmp_path / "records.py"
    path.write_text(RECORDS + COLLECT)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "ok", result
    diff = difftest_file(path, tmp_path / "diff", examples=40)
    assert diff.ok, diff


@pytest.mark.skipif(find_dafny() is None, reason="Dafny required")
def test_repeat_negative_lengths_and_negative_index_updates(tmp_path, monkeypatch):
    source = '''#@ ensures len(result) == max(0, n)
def repeat(n: int) -> list[int]:
    return [7] * n

#@ requires n > 0
#@ ensures len(result) == n
#@ ensures result[-1] == v
def replace(n: int, v: int) -> list[int]:
    xs = [0] * n
    xs[-1] = v
    return xs
'''
    path = tmp_path / "lists.py"
    path.write_text(source)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "ok", result
    # Keep generated list sizes bounded; arbitrary integers are proof inputs.
    source = source.replace("#@ ensures len(result) == max(0, n)", "#@ requires -10 <= n <= 10\n#@ ensures len(result) == max(0, n)").replace("n > 0", "0 < n <= 10")
    path.write_text(source)
    from hypothesis import strategies as st
    import veripy.difftest.harness as harness
    original_strategy = harness.strategy_for
    monkeypatch.setattr(harness, "strategy_for", lambda t, records=None:
                        st.integers(-10, 10) if t == "int" else original_strategy(t, records))
    diff = difftest_file(path, tmp_path / "diff", examples=25)
    assert diff.ok, diff


@pytest.mark.skipif(find_dafny() is None, reason="Dafny required")
def test_index_bounds_fail_at_python_write(tmp_path):
    source = "#@ ensures True\ndef bad(i: int) -> list[int]:\n    xs = [0]\n    xs[i] = 7\n    return xs\n"
    path = tmp_path / "bad.py"
    path.write_text(source)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "failed", result
    assert any(f["py_line"] == 4 for f in result["failures"]), result


def test_record_guards_deep_check_copy_and_preserve_values(tmp_path):
    source = RECORDS + COLLECT
    path = tmp_path / "guarded.py"
    path.write_text(emit_guarded(source, parse_source(source), "records.py", check_ensures=True))
    m = _load_original_module(path)
    req = m.Request(m.KV(4))
    assert m.collect([req, req]) == [4, 4]
    desc = ("list", ("record", "Request", (("kv", ("record", "KV", (("allocated", ("int",)),))),)))
    copied = guard_value([req, req], desc, function="collect", param="reqs",
                         record_types={"Request": m.Request, "KV": m.KV})
    assert copied[0] is not req and copied[0].kv is not req.kv
    # Exact types prevent descriptors/subclasses from replacing field reads.
    class Impostor(m.Request):
        pass
    with pytest.raises(TypeGuardError):
        m.collect([Impostor(req.kv)])
    object.__setattr__(req.kv, "allocated", True)
    assert copied[0].kv.allocated == 4 and copied[1].kv.allocated == 4
    with pytest.raises(TypeGuardError, match=r"reqs\[0\].kv.allocated"):
        m.collect([req])


@pytest.mark.skipif(find_dafny() is None, reason="Dafny required")
def test_record_results_round_trip_through_compiled_adapter(tmp_path):
    source = RECORDS + '''#@ ensures result == r
def identity(r: Request) -> Request:
    return r
'''
    path = tmp_path / "returned.py"
    path.write_text(source)
    result = verify(path, tmp_path / "proof")
    assert result["status"] == "ok", result
    diff = difftest_file(path, tmp_path / "diff", examples=20)
    assert diff.ok, diff


def test_planner_body_and_frozen_contracts():
    root = Path(__file__).resolve().parents[1] / "case_studies/repository_driven_v2/sglang-planner"
    original = ast.parse((root / "original.py").read_text()).body[0]
    current = next(n for n in ast.parse((root / "planner.py").read_text()).body if isinstance(n, ast.FunctionDef))
    assert [ast.dump(n) for n in original.body] == [ast.dump(n) for n in current.body]
