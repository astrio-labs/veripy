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


def test_generated_and_vendored_trees_are_not_swept(tmp_path):
    # None of these is hidden by FILENAME, so a name-only filter sweeps a
    # virtualenv's whole site-packages as corpus. Two things then break at
    # once: third-party files report as trouble, and their functions count
    # toward `compared` — the number --min-functions checks, so the floor
    # proving "the corpus is still covered" could be met by dependencies.
    _write(tmp_path / "task.py")
    _write(tmp_path / ".venv" / "lib" / "python3.12" / "site-packages" / "dep.py")
    _write(tmp_path / "__pycache__" / "cached.py")
    _write(tmp_path / "build" / "lib" / "generated.py")
    _write(tmp_path / "node_modules" / "vendored.py")
    _write(tmp_path / "lemmapy.egg-info" / "stale.py")
    assert [p.name for p in _difftest_targets([tmp_path])] == ["task.py"]


def test_explicit_files_pass_through_in_order(tmp_path):
    a = _write(tmp_path / "a.py")
    b = _write(tmp_path / "b.py")
    assert _difftest_targets([b, a]) == [b, a]


def test_naming_a_pruned_file_still_sweeps_it(tmp_path):
    # Pruning is about what a DIRECTORY expands to. Naming a file is the
    # intent, so it must not be silently dropped for where it lives.
    dep = _write(tmp_path / "build" / "generated.py")
    assert _difftest_targets([dep]) == [dep]


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


def test_unwritable_report_does_not_swallow_the_verdict(
        tmp_path, capsys, monkeypatch):
    # A --report path that cannot be written used to raise straight out of
    # the command. The sweep's whole result went with it, and an uncaught
    # exception exits 1 — the code that means DIVERGENCE — so a bad path on
    # a clean corpus would have been read as an encoder bug.
    src = _write(tmp_path / "a.py")
    _stub(monkeypatch, lambda n: [FunctionDiff("f", n)])
    blocker = tmp_path / "blocker"
    blocker.write_text("a file where a directory would have to be\n")
    assert cmd_difftest([src], tmp_path / "out", 10,
                        report=blocker / "report.json") == 2
    err = capsys.readouterr().err
    assert "could not write the difftest report" in err
    # and it is not green either: the record the nightly uploads never landed.


def test_divergence_survives_an_unwritable_report(tmp_path, monkeypatch):
    # The divergence is the finding; a failed report write must not reclassify
    # it as mere trouble.
    src = _write(tmp_path / "a.py")
    _stub(monkeypatch, lambda n: [FunctionDiff(
        "f", n, mismatch=Mismatch(args=(1,), python_result=0, dafny_result=1))])
    blocker = tmp_path / "blocker"
    blocker.write_text("not a directory\n")
    assert cmd_difftest([src], tmp_path / "out", 10,
                        report=blocker / "report.json") == 1


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


def _run_script_lines(text: str):
    """Yield (line number, line) for every line inside a `run:` block.

    GitHub substitutes `${{ }}` into the script TEXT before any shell exists,
    so an expression there is not an argument — it is source code. Reading the
    blocks off the indentation is enough to tell script from surrounding YAML
    without a YAML parser (there is none in the dev deps).
    """
    indent: int | None = None
    for number, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        here = len(line) - len(line.lstrip())
        if indent is not None:
            if stripped and here <= indent:
                indent = None       # dedented back out of the script
            else:
                yield number, line
                continue
        if stripped.startswith("run:"):
            indent = here
            yield number, line


def test_no_workflow_interpolates_an_expression_into_a_shell_script():
    # The sweep takes an `examples` count from workflow_dispatch. Interpolated
    # into `run:` it is whatever the person dispatching typed, pasted into the
    # script before the shell parses it; through `env:` it is one string that
    # argparse either accepts as an int or rejects.
    offenders = [
        f"{path.name}:{number}: {line.strip()}"
        for path in sorted((REPO / ".github" / "workflows").glob("*.yml"))
        for number, line in _run_script_lines(path.read_text())
        if "${{" in line and not line.lstrip().startswith("#")
    ]
    assert not offenders, (
        "workflow expression substituted into a shell script — pass it via "
        "`env:` and reference \"$VAR\" instead:\n  " + "\n  ".join(offenders))
