"""`lemmapy difftest` as a SWEEP: what it covers, and how it says so.

The harness itself is tested in test_difftest.py. These are about the
command a nightly job runs unattended, where the dangerous outcome is not
a crash but a green run that quietly stopped testing anything.
"""

import json
from pathlib import Path

from lemmapy.cli import _difftest_targets, cmd_difftest
from lemmapy.difftest.harness import DiffResult, FunctionDiff, Mismatch


def _write(path: Path, text: str = "x = 1\n") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path


def _stub(monkeypatch, functions):
    """Replace the harness so these tests exercise the sweep's bookkeeping
    rather than Dafny (which test_difftest.py covers)."""
    monkeypatch.setattr(
        "lemmapy.difftest.harness.difftest_file",
        lambda path, outdir, examples=100: DiffResult(
            path=str(path), functions=list(functions(examples))))


# -- what gets swept ---------------------------------------------------------

def test_directory_expands_recursively(tmp_path):
    _write(tmp_path / "a.py")
    _write(tmp_path / "pkg" / "b.py")
    _write(tmp_path / "notes.txt", "not python")
    assert [p.name for p in _difftest_targets([tmp_path])] == ["a.py", "b.py"]


def test_file_reachable_twice_is_compared_once(tmp_path):
    # Listed explicitly AND inside a listed directory: counting it twice
    # would inflate the coverage number the vacuity guard checks.
    a = _write(tmp_path / "a.py")
    assert _difftest_targets([a, tmp_path]) == [a]
    assert len(_difftest_targets([tmp_path, a])) == 1


def test_hidden_files_are_not_swept(tmp_path):
    _write(tmp_path / "a.py")
    _write(tmp_path / ".hidden.py")
    assert [p.name for p in _difftest_targets([tmp_path])] == ["a.py"]


def test_explicit_files_pass_through_in_order(tmp_path):
    a = _write(tmp_path / "a.py")
    b = _write(tmp_path / "b.py")
    assert _difftest_targets([b, a]) == [b, a]


# -- a sweep that stopped testing must not look like a sweep that passed -----

def test_sweeping_nothing_is_a_failure_not_a_pass(tmp_path, capsys):
    empty = tmp_path / "empty"
    empty.mkdir()
    assert cmd_difftest([empty], tmp_path / "out", 10) == 2
    assert "expected at least 1" in capsys.readouterr().err


def test_min_functions_catches_a_sweep_that_shrank(tmp_path, capsys, monkeypatch):
    # A corpus move or a stale path leaves the command comparing less than
    # it used to. Without a floor that reads as success.
    src = _write(tmp_path / "a.py")
    _stub(monkeypatch, lambda n: [FunctionDiff("f", n)])
    assert cmd_difftest([src], tmp_path / "out", 10, min_functions=1) == 0
    assert cmd_difftest([src], tmp_path / "out", 10, min_functions=5) == 2
    assert "compared 1 function(s), expected at least 5" in capsys.readouterr().err


def test_file_with_nothing_to_compare_is_reported_not_silent(
        tmp_path, capsys, monkeypatch):
    src = _write(tmp_path / "a.py")
    _stub(monkeypatch, lambda n: [])
    assert cmd_difftest([src], tmp_path / "out", 10) == 2
    out = capsys.readouterr().out
    assert "nothing to compare" in out and "1 with nothing to compare" in out


# -- the report a nightly uploads --------------------------------------------

def test_report_carries_the_reproducer(tmp_path, monkeypatch):
    src = _write(tmp_path / "a.py")
    _stub(monkeypatch, lambda n: [FunctionDiff(
        "pymod", n, mismatch=Mismatch(args=(1, -2), python_result=-1,
                                      dafny_result=1))])
    report = tmp_path / "r.json"
    assert cmd_difftest([src], tmp_path / "out", 10, report=report) == 1
    payload = json.loads(report.read_text())
    assert payload["schema"] == "lemmapy-difftest/1"
    assert payload["totals"] == {"files": 1, "compared": 1, "skipped": 0,
                                 "diverged": 1, "trouble": 0}
    # reprs, so the record survives JSON whatever the strategy produced --
    # and this record IS the reproducer for the encoder bug.
    assert payload["files"][0]["functions"][0]["mismatch"] == {
        "args": "(1, -2)", "python": "-1", "dafny": "1"}


def test_divergence_beats_the_coverage_floor(tmp_path, monkeypatch):
    # A run that both diverged AND compared too little must report the
    # divergence (exit 1), not hide it behind the coverage complaint.
    src = _write(tmp_path / "a.py")
    _stub(monkeypatch, lambda n: [FunctionDiff(
        "f", n, mismatch=Mismatch(args=(0,), python_result=0, dafny_result=1))])
    assert cmd_difftest([src], tmp_path / "out", 10, min_functions=99) == 1


# -- the nightly's coverage floor must stay tied to the real corpus ----------

REPO = Path(__file__).resolve().parent.parent


def _nightly_min_functions() -> int:
    import re

    text = (REPO / ".github" / "workflows" / "nightly.yml").read_text()
    match = re.search(r"--min-functions\s+(\d+)", text)
    assert match, "the nightly sweep no longer passes --min-functions"
    return int(match.group(1))


def test_nightly_floor_cannot_exceed_the_corpus():
    # A floor above what the corpus can supply makes the nightly red every
    # night for no reason, which is how a job stops being read at all.
    tasks = len(list((REPO / "benchmark" / "tasks").glob("*/task.py")))
    floor = _nightly_min_functions()
    assert floor <= tasks, (
        f"nightly --min-functions {floor} exceeds the {tasks} task(s) in "
        f"benchmark/tasks — the sweep cannot reach it")


def test_nightly_floor_has_not_been_defanged():
    # The opposite failure: dropping the floor to 1 to make a red job green
    # keeps the guard nominally present while removing everything it checked.
    tasks = len(list((REPO / "benchmark" / "tasks").glob("*/task.py")))
    floor = _nightly_min_functions()
    assert floor * 2 >= tasks, (
        f"nightly --min-functions {floor} covers under half of the {tasks} "
        f"corpus task(s); raise it or the sweep can silently stop testing "
        f"most of the corpus while still passing")
