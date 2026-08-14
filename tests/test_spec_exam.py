"""The spec-writing exam: strip specs, freeze the source, score spec strength."""

import json
from pathlib import Path

import pytest

from lemmapy.backends.dafny.driver import find_dafny
from lemmapy.benchmark.mutate import generate_mutations
from lemmapy.benchmark.specexam import (
    SpecExamError,
    check_frozen,
    golden_to_variant_map,
    render_spec_exam_report,
    run_spec_exam,
    strip_specs,
    translate_equivalents,
)
from lemmapy.cli import main
from lemmapy.repair import make_engine

REPO = Path(__file__).resolve().parent.parent
TASKS = REPO / "benchmark" / "tasks"

TASK_IDS = sorted(p.parent.name for p in TASKS.glob("*/task.py"))

MINI = (
    "#@ ensures result >= x\n"
    "#@ ensures result >= 0\n"
    "def clamp_low(x: int) -> int:\n"
    "    if x < 0:\n"
    "        return 0\n"
    "    return x\n"
)
MINI_STRIPPED = (
    "def clamp_low(x: int) -> int:\n"
    "    if x < 0:\n"
    "        return 0\n"
    "    return x\n"
)


def _mini_corpus(tmp_path, source=MINI, meta=None):
    corpus = tmp_path / "tasks"
    d = corpus / "mini"
    d.mkdir(parents=True)
    (d / "task.py").write_text(source)
    (d / "meta.json").write_text(json.dumps(meta or {"id": "mini"}))
    return corpus


def _engine_replaying(*answers):
    """An engine that returns the given answers in order."""
    state = {"i": 0}

    def engine(request):
        i = state["i"]
        state["i"] = i + 1
        return answers[min(i, len(answers) - 1)]

    return engine


# --- stripping -------------------------------------------------------------

@pytest.mark.parametrize("task_id", TASK_IDS)
def test_strip_specs_over_golden_corpus(task_id):
    import ast

    from lemmapy.benchmark.specexam import _spec_comment_lines

    source = (TASKS / task_id / "task.py").read_text()
    stripped = strip_specs(source)
    # No spec CLAUSES remain. (A literal "#@" may survive inside a
    # docstring — gcd's prose mentions `#@ proof` — and must, since it is
    # data, not a clause.)
    assert _spec_comment_lines(stripped) == {}
    # The executable program is untouched: comments are invisible to the
    # AST, so stripping them must not move a single node.
    assert ast.dump(ast.parse(stripped)) == ast.dump(ast.parse(source))
    # Surviving lines keep their order and text verbatim.
    spec_lines = _spec_comment_lines(source)
    kept = [ln for i, ln in enumerate(source.split("\n"), start=1)
            if i not in spec_lines]
    assert stripped.split("\n") == kept


@pytest.mark.parametrize("task_id", TASK_IDS)
def test_corpus_has_no_trailing_spec_comments(task_id):
    # The exam's correctness argument is that stripping is invertible, which
    # a `#@` trailing executable code would break. Pin the precondition.
    strip_specs((TASKS / task_id / "task.py").read_text())


def test_trailing_spec_comment_refused():
    with pytest.raises(SpecExamError, match="trailing executable code"):
        strip_specs("def f() -> int:\n    return 0  #@ ensures result == 0\n")


def test_hash_at_inside_string_is_not_a_spec_comment():
    # tokenize-driven, so `#@` inside a literal is data, not a clause.
    source = 'def f() -> str:\n    return "#@ ensures result == 0"\n'
    assert strip_specs(source) == source


def test_strip_proof_mode_keeps_other_clauses():
    source = (
        "#@ ensures result == x\n"
        "def f(x: int) -> int:\n"
        "    #@ proof Obvious(x)\n"
        "    return x\n"
    )
    kept = strip_specs(source, mode="proof")
    assert "#@ ensures" in kept and "#@ proof" not in kept


# --- source freeze ---------------------------------------------------------

def test_check_frozen_accepts_spec_reinsertion():
    violations, line_map = check_frozen(MINI_STRIPPED, MINI)
    assert violations == []
    # Stripped line 1 (`def ...`) sits at line 3 of the annotated file.
    assert line_map[1] == 3
    assert line_map[4] == 6


@pytest.mark.parametrize("mangled,needle", [
    # Edited executable line.
    ("#@ ensures result >= 0\n"
     "def clamp_low(x: int) -> int:\n"
     "    if x < 1:\n"
     "        return 0\n"
     "    return x\n", "changed"),
    # Deleted executable line.
    ("#@ ensures result >= 0\n"
     "def clamp_low(x: int) -> int:\n"
     "    return x\n", "line"),
    # Inserted blank line (AST-invisible, so text must be authoritative).
    ("#@ ensures result >= 0\n"
     "def clamp_low(x: int) -> int:\n"
     "\n"
     "    if x < 0:\n"
     "        return 0\n"
     "    return x\n", "line"),
])
def test_check_frozen_rejects_code_edits(mangled, needle):
    violations, _ = check_frozen(MINI_STRIPPED, mangled)
    assert violations, "a code edit must never pass the freeze check"
    assert needle in violations[0].message


def test_check_frozen_rejects_unparseable_answer():
    violations, _ = check_frozen(MINI_STRIPPED, "def clamp_low(:\n")
    assert violations and "does not parse" in violations[0].message


def test_check_frozen_catches_ast_invisible_edit():
    # An inserted blank line leaves the AST identical — the pair of checks
    # must disagree loudly rather than let it through.
    annotated = MINI.replace("def clamp_low", "\ndef clamp_low")
    violations, _ = check_frozen(MINI_STRIPPED, annotated)
    assert violations
    assert any("frozen too" in v.message or "changed" in v.message
               for v in violations)


# --- panel comparability (the load-bearing property) -----------------------

@pytest.mark.parametrize("task_id", TASK_IDS)
def test_panel_alignment_under_spec_insertion(task_id):
    """Golden and engine panels must be the SAME faults.

    The paper compares kill rates on "the identical panel". That holds
    because mutations sort by (line, col, replacement) and inserting `#@`
    lines is a monotone renumbering: order survives, so the max_mutants
    truncation picks the same sites. Pin it — a mutate.py change that broke
    this would silently invalidate every comparison.
    """
    golden = (TASKS / task_id / "task.py").read_text()
    stripped = strip_specs(golden)
    _, line_map = check_frozen(stripped, golden)
    golden_panel = generate_mutations(golden, max_mutants=8)
    stripped_panel = generate_mutations(stripped, max_mutants=8)
    assert len(golden_panel) == len(stripped_panel)
    for (g_desc, _), (s_desc, _) in zip(golden_panel, stripped_panel):
        s_line = int(s_desc.split(":")[0].removeprefix("line "))
        expected = g_desc.replace(
            f"line {line_map[s_line]}: ", f"line {s_line}: ", 1)
        assert s_desc == expected, (
            f"panel diverged: golden {g_desc!r} vs stripped {s_desc!r}")


def test_translate_equivalents_uses_the_line_map():
    meta = {"id": "max_element", "equivalent_mutants": ["line 17: `>` -> `>=`"]}
    out = translate_equivalents(meta, {17: 21})
    assert out["equivalent_mutants"] == ["line 21: `>` -> `>=`"]
    # The input is not mutated in place.
    assert meta["equivalent_mutants"] == ["line 17: `>` -> `>=`"]
    # An unmappable line keeps its original text, so the mismatch surfaces
    # as an un-excluded survivor instead of a silent exclusion.
    assert translate_equivalents(meta, {})["equivalent_mutants"] \
        == ["line 17: `>` -> `>=`"]


EQUIV_TASKS = [
    t for t in TASK_IDS
    if json.loads((TASKS / t / "meta.json").read_text()).get("equivalent_mutants")
]


def test_corpus_still_has_an_adjudication_case():
    assert EQUIV_TASKS, (
        "no task carries equivalent_mutants — the translation path would be "
        "untested; keep at least one adjudicated mutant in the corpus")


@pytest.mark.parametrize("task_id", EQUIV_TASKS)
@pytest.mark.parametrize("variant_name", ["golden", "reannotated", "stripped"])
def test_equivalents_translate_into_every_variant_panel(task_id, variant_name):
    """The exclusion must LAND, not merely be rewritten.

    `equivalent_mutants` are adjudicated against the golden file, but the
    exam scores differently-numbered variants. An untranslated (or
    half-translated) description silently fails to exclude, and the engine
    is charged for a mutant the golden run was forgiven — the comparison
    breaks quietly. This caught exactly that: a stripped->proposal map was
    applied to golden-numbered descriptions.
    """
    meta = json.loads((TASKS / task_id / "meta.json").read_text())
    golden = (TASKS / task_id / "task.py").read_text()
    stripped = strip_specs(golden)
    variants = {
        "golden": golden,
        "stripped": stripped,
        # A plausible engine answer: same code, differently placed specs.
        "reannotated": "#@ ensures True\n" + stripped,
    }
    variant = variants[variant_name]
    line_map = golden_to_variant_map(golden, stripped, variant)
    translated = translate_equivalents(meta, line_map)["equivalent_mutants"]
    panel = {d for d, _ in generate_mutations(variant, max_mutants=8)}
    assert set(translated) <= panel, (
        f"translated equivalents {translated} are not in the {variant_name} "
        f"panel {sorted(panel)} — the exclusion would silently miss")
    # And the count matches: every adjudicated mutant is still excluded.
    assert len(translated) == len(meta["equivalent_mutants"])


def test_translate_equivalents_uses_the_map_it_is_given():
    meta = {"id": "t", "equivalent_mutants": ["line 17: `>` -> `>=`"]}
    assert translate_equivalents(meta, {17: 21})["equivalent_mutants"] \
        == ["line 21: `>` -> `>=`"]


# --- validity and retries --------------------------------------------------

def test_retry_on_freeze_violation_then_valid(tmp_path, monkeypatch):
    import lemmapy.benchmark.specexam as spec_mod

    monkeypatch.setattr(spec_mod, "run_task", _fake_run_task(6, 3, 3))
    corpus = _mini_corpus(tmp_path)
    cheat = MINI.replace("if x < 0", "if x < 1")  # edits the implementation
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(cheat, MINI))
    assert score.valid and score.attempts == 2
    assert score.retry_reasons == ["freeze"]


def test_engine_cannot_weaken_the_implementation(tmp_path, monkeypatch):
    import lemmapy.benchmark.specexam as spec_mod

    monkeypatch.setattr(spec_mod, "run_task", _fake_run_task(6, 3, 3))
    corpus = _mini_corpus(tmp_path)
    # Rewrite the body to `return 0` and "prove" a trivial spec: rejected
    # every time, so the task scores invalid rather than perfect.
    cheat = ("#@ ensures result == 0\n"
             "def clamp_low(x: int) -> int:\n"
             "    return 0\n")
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(cheat), retries=1)
    assert not score.valid
    assert score.reason.startswith("freeze")
    assert score.attempts == 2  # the retry budget was spent, then given up


def test_proof_clause_rejected(tmp_path, monkeypatch):
    import lemmapy.benchmark.specexam as spec_mod

    monkeypatch.setattr(spec_mod, "run_task", _fake_run_task(6, 3, 3))
    corpus = _mini_corpus(tmp_path)
    with_proof = ("#@ ensures result >= 0\n"
                  "def clamp_low(x: int) -> int:\n"
                  "    #@ proof Magic(x)\n"
                  "    if x < 0:\n"
                  "        return 0\n"
                  "    return x\n")
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(with_proof), retries=0)
    assert not score.valid and "proof" in score.reason


def test_missing_ensures_rejected(tmp_path, monkeypatch):
    import lemmapy.benchmark.specexam as spec_mod

    monkeypatch.setattr(spec_mod, "run_task", _fake_run_task(6, 3, 3))
    corpus = _mini_corpus(tmp_path)
    only_requires = ("#@ requires x >= -10\n"
                     "def clamp_low(x: int) -> int:\n"
                     "    if x < 0:\n"
                     "        return 0\n"
                     "    return x\n")
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(only_requires),
                             retries=0)
    assert not score.valid and "ensures" in score.reason


def test_retry_feedback_carries_no_verification_outcome(tmp_path, monkeypatch):
    # Retries must never leak prover information — that would make this a
    # de-facto iterative proof exam rather than a spec-writing one.
    import lemmapy.benchmark.specexam as spec_mod

    monkeypatch.setattr(spec_mod, "run_task", _fake_run_task(6, 3, 3))
    corpus = _mini_corpus(tmp_path)
    seen = []

    def engine(request):
        seen.append(request)
        return MINI if len(seen) > 1 else "def broken(:\n"

    run_spec_exam(corpus, tmp_path / "work", lambda: engine)
    assert len(seen) == 2
    # Only the feedback channel may differ between attempts; the rules and
    # the frozen source are constant, so scope the leak check to feedback.
    assert seen[1]["rules"] == seen[0]["rules"]
    assert seen[1]["source"] == seen[0]["source"]
    feedback = json.dumps({"errors": seen[1]["errors"],
                           "history": seen[1]["history"]})
    assert "syntax" in feedback
    for leak in ("postcondition", "invariant", "counterexample", "verified",
                 "kill", "mutant", "dafny", "crosshair"):
        assert leak not in feedback.lower()


# --- scoring ---------------------------------------------------------------

def _fake_run_task(height, total, killed, survivors=()):
    from lemmapy.benchmark.runner import PASS, Rung, TaskScore

    def fake(task_dir, workdir, **kwargs):
        score = TaskScore(task_id=task_dir.parent.name)
        score.rungs = [Rung(n, PASS) for n in
                       ["gate", "hunt", "mutants", "encode", "prove",
                        "fidelity"][:height]]
        score.mutants_total = total
        score.mutants_killed = killed
        score.survivors = list(survivors)
        return score

    return fake


def test_weak_spec_scores_low_kill_rate(tmp_path, monkeypatch):
    # The anti-gaming property in one test: a worthless spec satisfies every
    # other checker (gate, hunt, encode, prove, fidelity — verified live in
    # docs/BENCHMARK.md) and only the panel reports it as empty.
    import lemmapy.benchmark.specexam as spec_mod

    calls = []
    real_fake = _fake_run_task(6, 3, 3)

    def fake(task_dir, workdir, **kwargs):
        calls.append(task_dir)
        score = real_fake(task_dir, workdir, **kwargs)
        if "scored" in str(task_dir):  # the engine's answer
            score.mutants_killed = 0
            score.survivors = ["line 4: `<` -> `<=`"]
        return score

    monkeypatch.setattr(spec_mod, "run_task", fake)
    corpus = _mini_corpus(tmp_path)
    weak = ("#@ ensures True\n"
            "def clamp_low(x: int) -> int:\n"
            "    if x < 0:\n"
            "        return 0\n"
            "    return x\n")
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(weak))
    assert score.valid and score.height == 6      # full ladder...
    assert score.kill_rate == 0.0                  # ...zero strength
    assert score.golden_kill_rate == 1.0
    assert score.survivors == ["line 4: `<` -> `<=`"]
    report = render_spec_exam_report([score])
    assert "0/3" in report and "3/3" in report


def test_unsound_spec_scores_zero_not_one_hundred(tmp_path, monkeypatch):
    """Writing a FALSE spec must never beat writing a true-but-weak one.

    A spec refuted at R1 short-circuits before the mutant panel, so the
    engine's own panel is 0/0. Scoring against that denominator drops the
    task from the engine's aggregate while golden still contributes its
    full panel — inverting the incentive. The denominator is golden's panel
    on every row.
    """
    import lemmapy.benchmark.specexam as spec_mod
    from lemmapy.benchmark.runner import FAIL, PASS, Rung, TaskScore

    def fake(task_dir, workdir, **kwargs):
        score = TaskScore(task_id="t")
        if "golden" in str(task_dir):
            score.rungs = [Rung(n, PASS) for n in
                           ["gate", "hunt", "mutants", "encode", "prove",
                            "fidelity"]]
            score.mutants_total = 4
            score.mutants_killed = 4
            return score
        # The engine's spec is refuted by CrossHair at R1: no panel runs.
        score.rungs = [Rung("gate", PASS), Rung("hunt", FAIL, "false when …")]
        score.mutants_total = 0
        score.mutants_killed = 0
        return score

    monkeypatch.setattr(spec_mod, "run_task", fake)
    corpus = _mini_corpus(tmp_path)
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(MINI))
    assert score.valid              # mechanically well-formed…
    assert score.mutants_total == 0  # …but its own panel never ran
    assert score.scored_total == 4   # scored against GOLDEN's panel
    assert score.kill_rate == 0.0    # not None, and emphatically not 1.0
    report = render_spec_exam_report([score])
    assert "0/4" in report
    assert "engine 0/4" in report


def test_invalid_answer_also_scores_against_golden_panel(tmp_path, monkeypatch):
    import lemmapy.benchmark.specexam as spec_mod

    monkeypatch.setattr(spec_mod, "run_task", _fake_run_task(6, 4, 4))
    corpus = _mini_corpus(tmp_path)
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying("def broken(:\n"),
                             retries=0)
    assert not score.valid
    assert score.scored_total == 4 and score.mutants_killed == 0
    assert "0/4" in render_spec_exam_report([score])


def test_crashes_are_not_credited_as_spec_strength(tmp_path, monkeypatch):
    # A mutant the INTERPRETER catches is caught equally by `ensures True`,
    # so it carries no information about the specification and is reported
    # separately rather than counted.
    import lemmapy.benchmark.specexam as spec_mod
    from lemmapy.benchmark.runner import PASS, Rung, TaskScore

    def fake(task_dir, workdir, **kwargs):
        score = TaskScore(task_id="t")
        score.rungs = [Rung(n, PASS) for n in ["gate", "hunt", "mutants"]]
        score.mutants_total = 4
        if "golden" in str(task_dir):
            score.mutants_killed = 4
        else:
            score.mutants_killed = 0
            score.mutants_crashed = 3   # all "kills" were crashes
            score.survivors = ["line 4: `<` -> `<=`"]
        return score

    monkeypatch.setattr(spec_mod, "run_task", fake)
    corpus = _mini_corpus(tmp_path)
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(MINI))
    assert score.kill_rate == 0.0 and score.mutants_crashed == 3
    report = render_spec_exam_report([score])
    assert "engine 0/4" in report
    assert "crashed" in report and "never credited" in report


def test_no_sidecar_is_staged_for_scoring(tmp_path, monkeypatch):
    # A stale sidecar in the scored dir would hand the run lemmas nobody
    # earned; assert on what run_task actually sees.
    import lemmapy.benchmark.specexam as spec_mod

    seen = []

    def fake(task_dir, workdir, **kwargs):
        seen.append(sorted(p.name for p in task_dir.iterdir()))
        return _fake_run_task(6, 3, 3)(task_dir, workdir, **kwargs)

    monkeypatch.setattr(spec_mod, "run_task", fake)
    corpus = _mini_corpus(tmp_path)
    (corpus / "mini" / "task.proofs.dfy").write_text("lemma L() {}\n")
    run_spec_exam(corpus, tmp_path / "work", lambda: _engine_replaying(MINI))
    assert seen, "run_task must have been called"
    for entries in seen:
        assert "task.proofs.dfy" not in entries
        assert entries == ["meta.json", "task.py"]


def test_golden_baseline_runs_under_exam_conditions(tmp_path, monkeypatch):
    # Fairness: the golden is scored with its `#@ proof` clauses stripped
    # and no sidecar, so the engine is not compared against a run that had
    # lemmas available.
    import lemmapy.benchmark.specexam as spec_mod

    sources = {}

    def fake(task_dir, workdir, **kwargs):
        sources[str(task_dir)] = (task_dir / "task.py").read_text()
        return _fake_run_task(6, 3, 3)(task_dir, workdir, **kwargs)

    monkeypatch.setattr(spec_mod, "run_task", fake)
    source = ("#@ ensures result == x\n"
              "def f(x: int) -> int:\n"
              "    #@ proof Obvious(x)\n"
              "    return x\n")
    corpus = _mini_corpus(tmp_path, source=source)
    run_spec_exam(corpus, tmp_path / "work",
                  lambda: _engine_replaying(
                      "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n"))
    golden_src = next(v for k, v in sources.items() if "golden" in k)
    assert "#@ ensures" in golden_src and "#@ proof" not in golden_src


def test_spec_exam_refuses_corpus_overlap(tmp_path):
    corpus = _mini_corpus(tmp_path)
    with pytest.raises(ValueError, match="overlaps the task corpus"):
        run_spec_exam(corpus, corpus / "work", lambda: _engine_replaying(MINI))
    assert (corpus / "mini" / "task.py").exists()


def test_empty_roster_renders_honestly():
    assert "no tasks" in render_spec_exam_report([])


# --- full stack ------------------------------------------------------------

def _full_stack_available() -> bool:
    import shutil

    return find_dafny() is not None and shutil.which("basedpyright") is not None


@pytest.mark.skipif(not _full_stack_available(), reason="dafny/basedpyright missing")
def test_golden_specs_replayed_score_like_golden(tmp_path):
    # End-to-end sanity: an engine that replays the golden annotations must
    # reproduce the golden kill rate exactly — if it does not, the panels
    # are not aligned and every comparison in the paper is meaningless.
    task = TASKS / "clamp"
    corpus = tmp_path / "tasks"
    (corpus / "clamp").mkdir(parents=True)
    (corpus / "clamp" / "task.py").write_text((task / "task.py").read_text())
    (corpus / "clamp" / "meta.json").write_text((task / "meta.json").read_text())
    golden_source = (task / "task.py").read_text()
    (score,) = run_spec_exam(corpus, tmp_path / "work",
                             lambda: _engine_replaying(golden_source),
                             mutant_cap=4, hunt_timeout=5,
                             dafny_time_limit=30, difftest_examples=10)
    assert score.valid
    assert score.mutants_total == score.golden_mutants_total
    assert score.mutants_killed == score.golden_mutants_killed
    assert score.height == score.golden_height


@pytest.mark.skipif(not _full_stack_available(), reason="dafny/basedpyright missing")
def test_cli_spec_writing_exit_codes(tmp_path, capsys):
    corpus = tmp_path / "tasks"
    (corpus / "clamp").mkdir(parents=True)
    (corpus / "clamp" / "task.py").write_text(
        (TASKS / "clamp" / "task.py").read_text())
    (corpus / "clamp" / "meta.json").write_text(
        (TASKS / "clamp" / "meta.json").read_text())
    empty = tmp_path / "empty"
    empty.mkdir()
    status = main(["benchmark", "--tasks", str(corpus), "-o", str(tmp_path / "o"),
                   "--exam", "spec-writing", "--engine", f"file:{empty}",
                   "--quick"])
    assert status == 1  # engine exhausted -> invalid, not a crash
    assert "valid: 0/1" in capsys.readouterr().out
