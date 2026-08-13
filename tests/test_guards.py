"""Boundary guards vs the §1 attack gallery (ARCHITECTURE): every attack
must be demonstrably stopped at the boundary, with the right blame."""

import importlib.util
import json
import sys
from pathlib import Path
from typing import cast
from unittest import mock

import pytest

from lemmapy.cli import cmd_guard
from lemmapy.frontend.extract import parse_source
from lemmapy.guards.emitter import GuardGenError, emit_guarded
from lemmapy.guards.runtime import (
    PostconditionError,
    PreconditionError,
    TypeGuardError,
)

CLAMP = (
    "#@ verified\n"
    "#@ requires lo <= hi\n"
    "#@ ensures lo <= result <= hi\n"
    "def clamp(x: int, lo: int, hi: int) -> int:\n"
    "    return min(max(x, lo), hi)\n"
)

INCR = (
    "#@ verified\n"
    "#@ ensures len(result) == len(xs)\n"
    "#@ ensures forall i in range(len(xs)) :: result[i] == xs[i] + 1\n"
    "def incr_list(xs: list[int]) -> list[int]:\n"
    "    out: list[int] = []\n"
    "    for i in range(len(xs)):\n"
    "        out.append(xs[i] + 1)\n"
    "    return out\n"
)

IDENT = (
    "#@ ensures len(result) == len(xs)\n"
    "def same(xs: list[int]) -> list[int]:\n"
    "    return xs\n"
)


def _load_guarded(tmp_path: Path, source: str, name: str = "m",
                  check_ensures: bool = False):
    src = tmp_path / f"{name}.py"
    src.write_text(source)
    outdir = tmp_path / "guarded"
    assert cmd_guard([src], outdir, check_ensures=check_ensures) == 0
    path = outdir / f"{name}_guarded.py"
    spec = importlib.util.spec_from_file_location(f"{name}_guarded_{tmp_path.name}", path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


# ---- attack gallery -----------------------------------------------------------


def test_json_smuggled_bool_rejected(tmp_path):
    # json.loads('true') is a bool; bool is an int subclass, but the proof
    # modeled int — exactness rejects it, naming the element path.
    mod = _load_guarded(tmp_path, INCR)
    payload = json.loads("[1, 2, true]")
    with pytest.raises(TypeGuardError, match=r"xs\[2\]: expected int, got bool"):
        mod.incr_list(payload)


def test_json_smuggled_float_rejected(tmp_path):
    mod = _load_guarded(tmp_path, INCR)
    with pytest.raises(TypeGuardError, match=r"xs\[0\]: expected int, got float"):
        mod.incr_list(json.loads("[1.0]"))


def test_typing_cast_lie_rejected(tmp_path):
    # cast() is a type-checker no-op; the guard checks the actual values.
    mod = _load_guarded(tmp_path, INCR)
    lied = cast("list[int]", ["a", "b"])
    with pytest.raises(TypeGuardError, match=r"xs\[0\]: expected int, got str"):
        mod.incr_list(lied)


def test_evil_list_subclass_rejected(tmp_path):
    class EvilList(list):
        def __getitem__(self, i):
            return -999

        def __len__(self):
            return 0

    mod = _load_guarded(tmp_path, INCR)
    with pytest.raises(TypeGuardError, match="expected list"):
        mod.incr_list(EvilList([1, 2, 3]))


def test_copy_in_severs_caller_alias(tmp_path):
    # The island receives a fresh list: even a function that returns its
    # argument cannot hand the caller's own object back through the boundary.
    mod = _load_guarded(tmp_path, IDENT)
    mine = [1, 2, 3]
    out = mod.same(mine)
    assert out == mine and out is not mine


def test_mock_patch_on_original_cannot_reach_island(tmp_path):
    # The guarded module carries a verbatim island copy; patching the
    # original module's function does not change what the boundary runs.
    src = tmp_path / "orig.py"
    src.write_text(CLAMP)
    outdir = tmp_path / "guarded"
    assert cmd_guard([src], outdir) == 0
    sys.path.insert(0, str(tmp_path))
    try:
        import orig  # noqa: F401

        spec = importlib.util.spec_from_file_location(
            "orig_guarded", outdir / "orig_guarded.py")
        guarded = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(guarded)
        with mock.patch.object(sys.modules["orig"], "clamp", lambda *a: -999):
            assert sys.modules["orig"].clamp(5, 0, 10) == -999  # attack works there
            assert guarded.clamp(5, 0, 10) == 5  # island unaffected
    finally:
        sys.path.remove(str(tmp_path))
        sys.modules.pop("orig", None)


def test_precondition_blames_caller(tmp_path):
    mod = _load_guarded(tmp_path, CLAMP)
    with pytest.raises(PreconditionError, match=r"requires lo <= hi.*blame: caller"):
        mod.clamp(5, 10, 0)


def test_ensures_check_blames_callee_or_toolchain(tmp_path):
    buggy = (
        "#@ requires lo <= hi\n"
        "#@ ensures lo <= result <= hi\n"
        "def clamp(x: int, lo: int, hi: int) -> int:\n"
        "    return x\n"
    )
    mod = _load_guarded(tmp_path, buggy, check_ensures=True)
    with pytest.raises(PostconditionError, match="callee-or-toolchain"):
        mod.clamp(-5, 0, 10)


# ---- behavior preservation ----------------------------------------------------


def test_valid_inputs_pass_through_unchanged(tmp_path):
    mod = _load_guarded(tmp_path, CLAMP, check_ensures=True)
    for x, lo, hi in ((5, 0, 10), (-5, 0, 10), (15, 0, 10), (0, 0, 0)):
        assert mod.clamp(x, lo, hi) == min(max(x, lo), hi)


def test_quantified_requires_evaluates(tmp_path):
    sorted_req = (
        "#@ requires forall i in range(len(xs) - 1) :: xs[i] <= xs[i + 1]\n"
        "#@ ensures result >= 0\n"
        "def first_or_zero(xs: list[int]) -> int:\n"
        "    return 0\n"
    )
    mod = _load_guarded(tmp_path, sorted_req)
    assert mod.first_or_zero([1, 2, 3]) == 0
    with pytest.raises(PreconditionError):
        mod.first_or_zero([3, 1, 2])


def test_optional_and_kwonly_supported(tmp_path):
    src = (
        "#@ ensures result >= 0\n"
        "def f(x: int | None, *, floor: int) -> int:\n"
        "    if x is None:\n"
        "        return floor if floor >= 0 else 0\n"
        "    return x if x >= 0 else 0\n"
    )
    mod = _load_guarded(tmp_path, src)
    assert mod.f(None, floor=3) == 3
    assert mod.f(7, floor=0) == 7
    with pytest.raises(TypeGuardError, match="expected int, got str"):
        mod.f("no", floor=0)


def test_old_in_ensures_uses_precall_copy(tmp_path):
    src = (
        "#@ ensures result == old(x) + 1\n"
        "def bump(x: int) -> int:\n"
        "    return x + 1\n"
    )
    mod = _load_guarded(tmp_path, src, check_ensures=True)
    assert mod.bump(4) == 5


# ---- adversarial round regressions --------------------------------------------


def test_lemmapy_prefixed_names_rejected():
    # A param named like a generated temporary silently substituted caller
    # arguments (_lemmapy_old_x collided with the old() snapshot; a param
    # named _lemmapy_island_f shadowed the island alias).
    for src in (
        "#@ ensures result >= old(x)\n"
        "def combine(x: int, _lemmapy_old_x: int) -> int:\n"
        "    return x + _lemmapy_old_x\n",
        "#@ ensures result >= 0\n"
        "def f(_lemmapy_island_f: int) -> int:\n"
        "    return 0\n",
        "_lemmapy_thing = 1\n"
        "#@ ensures result >= 0\n"
        "def f(x: int) -> int:\n"
        "    return 0\n",
    ):
        with pytest.raises(GuardGenError, match="reserved for generated"):
            emit_guarded(src, parse_source(src), src_name="m.py", check_ensures=True)


def test_old_text_inside_string_literal_not_rewritten(tmp_path):
    # The old() rewrite is AST-based: 'old(x)' inside a string literal is
    # data, not a snapshot reference. Both directions: the check must fire
    # on a violation and stay quiet on satisfaction.
    src = (
        '#@ ensures result != "old(x)"\n'
        "def f(x: int) -> str:\n"
        '    return "old(x)"\n'
    )
    mod = _load_guarded(tmp_path, src, check_ensures=True)
    with pytest.raises(PostconditionError):
        mod.f(1)
    src_ok = (
        '#@ ensures result == "old(x)"\n'
        "def g(x: int) -> str:\n"
        '    return "old(x)"\n'
    )
    mod = _load_guarded(tmp_path, src_ok, name="m2", check_ensures=True)
    assert mod.g(1) == "old(x)"


def test_requires_evaluation_error_becomes_precondition_blame(tmp_path):
    src = (
        "#@ requires max(xs) >= 0\n"
        "#@ ensures result >= 0\n"
        "def f(xs: list[int]) -> int:\n"
        "    return 0\n"
    )
    mod = _load_guarded(tmp_path, src)
    with pytest.raises(PreconditionError, match="raised ValueError.*blame: caller"):
        mod.f([])


def test_nested_def_cannot_be_guarded():
    src = (
        "def outer() -> None:\n"
        "    #@ ensures result >= 0\n"
        "    def inner(x: int) -> int:\n"
        "        return x\n"
    )
    with pytest.raises(GuardGenError, match="module-level"):
        emit_guarded(src, parse_source(src), src_name="m.py")


def test_lone_surrogate_string_rejected(tmp_path):
    src = (
        "#@ ensures result >= 0\n"
        "def f(s: str) -> int:\n"
        "    return len(s)\n"
    )
    mod = _load_guarded(tmp_path, src)
    assert mod.f("héllo") == 5
    with pytest.raises(TypeGuardError, match="lone surrogate"):
        mod.f("a\ud800b")


def test_island_mutation_cannot_fool_ensures(tmp_path):
    # The island receives its own copy when ensures are checked, so an
    # island that mutates its parameter cannot change what the
    # postcondition evaluates against.
    src = (
        "#@ ensures len(xs) == 1\n"
        "def f(xs: list[int]) -> int:\n"
        "    xs.append(0)\n"
        "    return 0\n"
    )
    mod = _load_guarded(tmp_path, src, check_ensures=True)
    assert mod.f([7]) == 0  # ensures reads the pre-call value: len 1


# ---- generator hygiene --------------------------------------------------------


def test_future_imports_rejected(tmp_path):
    src = "from __future__ import annotations\n" + CLAMP
    specs = parse_source(src)
    with pytest.raises(GuardGenError, match="__future__"):
        emit_guarded(src, specs, src_name="m.py")


def test_unspecced_module_refuses_to_guard():
    src = "def f() -> int:\n    return 0\n"
    with pytest.raises(GuardGenError, match="no spec'd functions"):
        emit_guarded(src, parse_source(src), src_name="m.py")


def test_guarded_corpus_imports_cleanly(tmp_path):
    # Every benchmark task must guard and import without error.
    tasks = sorted(Path("benchmark/tasks").glob("*/task.py"))
    assert len(tasks) >= 12
    outdir = tmp_path / "guarded"
    for i, task in enumerate(tasks):
        target = tmp_path / f"task_{task.parent.name}.py"
        target.write_text(task.read_text())
        assert cmd_guard([target], outdir) == 0
        path = outdir / f"task_{task.parent.name}_guarded.py"
        spec = importlib.util.spec_from_file_location(f"gtask{i}", path)
        mod = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(mod)
