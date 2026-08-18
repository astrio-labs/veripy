"""The Lean backend, slice 1: loop-free integer functions behind the
`ProofBackend` seam.

Split by dependency: encoder and classifier tests are pure Python (they
run everywhere, CI included); end-to-end tests need `lean` on PATH and
carry the house skipif. Every live assertion here was first pinned
against a real Lean 4.33 run.
"""

from pathlib import Path

import pytest

from lemmapy.backends.base import available_backends, get_backend
from lemmapy.backends.dafny.encoder import EncodeError
from lemmapy.backends.lean.backend import LeanBackend
from lemmapy.backends.lean.driver import classify_lean_message, find_lean
from lemmapy.backends.lean.encoder import encode_module_lean
from lemmapy.frontend.extract import parse_source

BUMP = ("#@ ensures result == x + 1\n"
        "def bump(x: int) -> int:\n"
        "    return x + 1\n")

CLAMP = ("#@ requires lo <= hi\n"
         "#@ ensures lo <= result <= hi\n"
         "def clamp(x: int, lo: int, hi: int) -> int:\n"
         "    if x < lo:\n"
         "        return lo\n"
         "    if x > hi:\n"
         "        return hi\n"
         "    return x\n")


def _encode(source: str):
    return encode_module_lean(source, parse_source(source),
                              module_name="m.py")


def test_registry_serves_lean():
    assert "lean" in available_backends()
    be = get_backend("lean")
    assert isinstance(be, LeanBackend)
    assert be is get_backend("lean")
    assert be.artifact_name("task") == "task.lean"
    assert be.sidecar_path(Path("/x/t.py")) == Path("/x/t.proofs.lean")


def test_encoder_emits_def_and_spec_theorem():
    enc = _encode(BUMP)
    assert "def «bump» («x» : Int) : Int :=" in enc.lean_source
    assert "theorem «bump_spec» («x» : Int) :" in enc.lean_source
    assert "(«bump» «x») = («x» + 1)" in enc.lean_source
    assert enc.theorems == ["bump_spec"]
    # The tactic lines map to the ensures clause, so a failing proof
    # points at the contract, not at Lean plumbing.
    tactic_line = next(i for i, text in
                       enumerate(enc.lean_source.split("\n"), start=1)
                       if "first | omega" in text)  # the endgame line
    assert enc.line_map[tactic_line] == 1  # ensures is source line 1


def test_encoder_compiles_if_chains_and_requires():
    enc = _encode(CLAMP)
    assert "if («x» < «lo») then «lo» else" in enc.lean_source
    assert "(h0 : («lo» ≤ «hi»))" in enc.lean_source
    # The chained comparison becomes a conjunction over the application.
    assert "(«clamp» «x» «lo» «hi»)" in enc.lean_source
    assert "∧" in enc.lean_source


def test_encoder_rejects_out_of_slice_loudly():
    loops = ("#@ ensures result >= 0\n"
             "def f(n: int) -> int:\n"
             "    s = 0\n"
             "    for i in range(n):\n"
             "        s = s + i\n"
             "    return s\n")
    with pytest.raises(EncodeError) as exc:
        _encode(loops)
    assert exc.value.rule == "lean-slice-1"
    assert "loop" in exc.value.message.lower()

    reassign = ("#@ ensures result == x\n"
                "def f(x: int) -> int:\n"
                "    x = x + 1\n"
                "    return x - 1\n")
    with pytest.raises(EncodeError, match="immutable"):
        _encode(reassign)


def test_escaped_identifiers_make_keyword_collisions_unrepresentable():
    # A keyword BLOCKLIST is inherently incomplete (`forall` escaped the
    # first draft's list; any future Lean keyword escapes it forever), so
    # every user identifier is emitted as «name» instead: a Python
    # function named `theorem`, a parameter named `then`, a local named
    # `have`, and a `def PyAbs` (prelude shadow) all ENCODE — the
    # collision class is unrepresentable, not enumerated.
    keyworded = ("#@ requires then >= 0\n"
                 "#@ ensures result == then + 1\n"
                 "def theorem(then: int) -> int:\n"
                 "    have = then + 1\n"
                 "    return have\n")
    enc = _encode(keyworded)
    assert "def «theorem» («then» : Int)" in enc.lean_source
    assert "let «have» :=" in enc.lean_source

    # Escaping does NOT separate user names from the prelude («PyAbs» IS
    # the identifier PyAbs — measured: "`PyAbs` has already been
    # declared"); the NAMESPACE does. A user `def PyAbs` coexists with
    # the prelude because call sites reference LemmaPy.PyAbs qualified,
    # which no top-level def redeclares and no binder captures.
    shadows_prelude = ("#@ ensures result == abs(a)\n"
                       "def PyAbs(a: int) -> int:\n"
                       "    return abs(a)\n")
    enc2 = _encode(shadows_prelude)
    assert "def «PyAbs»" in enc2.lean_source          # user def, escaped
    assert "(LemmaPy.PyAbs «a»)" in enc2.lean_source  # abs() -> qualified


def test_param_shadowing_is_allowed_and_alpha_renamed_in_theorems():
    # A binder shadowing a top-level name is legal Lean and matches
    # Python scoping, so `def f(f: int)` and a parameter named after a
    # DIFFERENT function must encode (the first draft rejected both
    # against the module-wide reservation set). The one genuine capture —
    # the theorem references the function AND its parameters by name —
    # is alpha-renamed: the theorem binds «f'» beside the function «f».
    own = ("#@ requires f >= 0\n"
           "#@ ensures result == f + 1\n"
           "def f(f: int) -> int:\n"
           "    return f + 1\n")
    enc = _encode(own)
    assert "def «f» («f» : Int)" in enc.lean_source       # def: shadow ok
    assert "theorem «f_spec» («f'» : Int)" in enc.lean_source
    assert "(«f» «f'») = («f'» + 1)" in enc.lean_source   # app + renamed use
    assert "(h0 : («f'» ≥ 0))" in enc.lean_source

    other = ("#@ ensures result == g\n"
             "def f(g: int) -> int:\n"
             "    return g\n"
             "\n"
             "#@ ensures result == x\n"
             "def g(x: int) -> int:\n"
             "    return x\n")
    enc2 = _encode(other)  # must not raise
    assert "def «f» («g» : Int)" in enc2.lean_source


def test_encoder_emits_bool_predicates_and_quantifiers():
    # Slice 2: predicate functions bridge Bool via decide, ensures
    # `result == X` becomes an iff against X-as-Prop, and forall/exists
    # over ranges become bounded ∀/∃.
    pred = ("#@ ensures result == (x > 0)\n"
            "def pos(x: int) -> bool:\n"
            "    return x > 0\n")
    enc = _encode(pred)
    assert "def «pos» («x» : Int) : Bool :=" in enc.lean_source
    assert "(decide (" in enc.lean_source
    assert "((«pos» «x») = true) ↔" in enc.lean_source

    quant = ("#@ requires n >= 0\n"
             "#@ ensures forall i in range(0, n) :: result >= i - n + 1\n"
             "def top(n: int) -> int:\n"
             "    return n\n")
    enc2 = _encode(quant)
    assert "(∀ «i» : Int, (0 ≤ «i» ∧ «i» < «n») →" in enc2.lean_source

    ex = ("#@ ensures exists i in range(0, 3) :: result == i\n"
          "def z(n: int) -> int:\n"
          "    return 0\n")
    enc3 = _encode(ex)
    assert "(∃ «i» : Int, (0 ≤ «i» ∧ «i» < 3) ∧" in enc3.lean_source

    # Out-of-slice quantifier shapes refuse loudly.
    with pytest.raises(EncodeError, match="range"):
        _encode("#@ ensures forall v in xs :: v >= 0\n"
                "def f(xs: int) -> int:\n"
                "    return xs\n")


def test_quantifier_binder_capture_is_alpha_renamed_transitively():
    # Soundness: a binder sharing a name with the function, a parameter,
    # or — the residual bug — a RENAMED theorem binder would capture the
    # `result` application and make Lean verify a different contract.
    # def f(f) renames the theorem param to f'; a quantifier binder f
    # must therefore land on f'' (measured: f' captured the renamed
    # param and a TRUE spec failed while proving the wrong goal).
    src = ("#@ requires f == 5\n"
           "#@ ensures forall f in range(0, 1) :: result >= f + 5\n"
           "def f(f: int) -> int:\n"
           "    return f\n")
    enc = _encode(src)
    assert "∀ «f''» : Int" in enc.lean_source
    assert "(«f» «f'») ≥ («f''» + 5)" in enc.lean_source


def test_shadowed_builtins_are_refused_not_mistranslated():
    # Soundness: Python calls the shadowing binding; translating to the
    # builtin would certify mathematical abs/min/max for a program that
    # never runs them.
    local_shadow = ("#@ ensures result >= 0\n"
                    "def h(x: int) -> int:\n"
                    "    abs = x\n"
                    "    return abs(x)\n")
    with pytest.raises(EncodeError, match="shadowed"):
        _encode(local_shadow)

    module_shadow = ("#@ ensures result == x\n"
                     "def abs(x: int) -> int:\n"
                     "    return x\n")
    with pytest.raises(EncodeError, match="encoder builtin"):
        _encode(module_shadow)

    range_shadow = ("#@ ensures forall i in range(0, range) :: result >= 0\n"
                    "def r(range: int) -> int:\n"
                    "    return 1\n")
    with pytest.raises(EncodeError, match="shadow"):
        _encode(range_shadow)


def test_classifier_maps_endgame_tactic_failures():
    # The endgame combinator reports its LAST sub-tactic's failure, not
    # omega's phrasing (measured: false specs reclassified as unknown
    # when the cocktail grew `first | omega | trivial`). The turnstile
    # needle is the robust form: any displayed unsolved goal is the spec
    # theorem failing.
    assert classify_lean_message(
        "Tactic `assumption` failed\n\nx : Int\n⊢ False") == "postcondition"
    assert classify_lean_message("some tactic\n⊢ x + 1 = x + 2") == "postcondition"


def test_encoder_rejects_cross_declaration_collisions():
    # The one collision escaping cannot remove: two EMITTED declarations
    # with the same name (`def f` beside `def f_spec`, whose generated
    # theorem is also «f_spec»).
    theorem_clash = ("#@ ensures result == x\n"
                     "def f(x: int) -> int:\n"
                     "    return x\n"
                     "\n"
                     "#@ ensures result == x\n"
                     "def f_spec(x: int) -> int:\n"
                     "    return x\n")
    with pytest.raises(EncodeError, match="collides"):
        _encode(theorem_clash)


def test_encoder_rejects_signature_forms_it_cannot_emit():
    # Defaults, *args/**kwargs, positional-only and keyword-only markers
    # were previously ERASED from the binder list — a wrong-arity Lean
    # artifact, or phantom unknown-name rejections for real parameters.
    for src in (
        "#@ ensures result == x\ndef f(x: int = 3) -> int:\n    return x\n",
        "#@ ensures result == x\ndef f(x: int, *, y: int) -> int:\n    return x\n",
        "#@ ensures result == x\ndef f(x: int, /) -> int:\n    return x\n",
        # *args is refused upstream by the frontend ("outside the
        # fragment") before this encoder runs — either guard is fine, as
        # long as SOMETHING refuses loudly.
        "#@ ensures result == x\ndef f(x: int, *a: int) -> int:\n    return x\n",
    ):
        with pytest.raises(EncodeError, match="slice 1|outside the fragment"):
            _encode(src)


def test_driver_reports_toolless_exit_as_tool_error(monkeypatch):
    # Nonzero exit with no parsed diagnostic is the TOOL failing, not a
    # proof — reporting `failed` would fabricate an unknown obligation
    # and send a repair loop after a proof that was never judged.
    import lemmapy.backends.lean.driver as driver_mod

    class Proc:
        returncode = 134
        stdout = ""
        stderr = "lean: internal panic"

    monkeypatch.setattr(driver_mod.subprocess, "run",
                        lambda *a, **k: Proc())
    monkeypatch.setattr(driver_mod, "find_lean", lambda: "/fake/lean")
    result = driver_mod.verify_lean_file(Path("/tmp/x.lean"), {})
    assert result.ok is False
    assert result.error is not None and "134" in result.error
    assert "panic" in result.error


def test_classifier_maps_live_lean_messages():
    # Pinned from live Lean 4.33 output: omega's failure text, which is
    # NOT "unsolved goals" (the first classifier draft missed it and a
    # false spec came back kind=unknown).
    assert classify_lean_message(
        "omega could not prove the goal:\nNo usable constraints found."
    ) == "postcondition"
    assert classify_lean_message("unsolved goals\n⊢ False") == "postcondition"
    assert classify_lean_message("unknown identifier 'PyFoo'") == "resolution"
    assert classify_lean_message(
        "(deterministic) timeout at `whnf`, maxHeartbeats") == "timeout"
    assert classify_lean_message("something novel") == "unknown"


def test_lean_sidecars_are_refused_not_ignored(tmp_path):
    # A user who wrote lemmas must never believe they were used.
    src = tmp_path / "t.py"
    src.write_text(BUMP)
    (tmp_path / "t.proofs.lean").write_text("theorem helper : True := trivial\n")
    be = get_backend("lean")
    with pytest.raises(EncodeError, match="P3"):
        be.load_sidecar(src)
    with pytest.raises(EncodeError, match="P3"):
        be.validate_sidecar("lemma L : True := trivial")
    be.validate_sidecar("")  # the empty sidecar every slice-1 run stages


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_true_spec_verifies(tmp_path):
    from lemmapy.agentio import verify_structured

    src = tmp_path / "m.py"
    src.write_text(CLAMP)
    payload = verify_structured(src, tmp_path / "out", backend="lean")
    assert payload["status"] == "ok"
    assert payload["toolchain"]["dafny_version"]  # lean's version string

    # A module with a LOCAL binding must also prove: omega does not look
    # through the `let`s the body compiler emits, and the tactic script's
    # `try dsimp only` exists precisely for this (measured: a one-local
    # module failed with the local itself in omega's counterexample,
    # while `dsimp only` without `try` regressed let-free clamp).
    local = tmp_path / "local.py"
    local.write_text("#@ ensures result == x + 2\n"
                     "def g(x: int) -> int:\n"
                     "    y = x + 1\n"
                     "    return y + 1\n")
    payload2 = verify_structured(local, tmp_path / "out2", backend="lean")
    assert payload2["status"] == "ok"

    # A module that SHADOWS the prelude while USING it: `def PyAbs`
    # calling abs(). Exercises the namespace separation (measured
    # collision without it) AND the tactic script's prelude unfold
    # (measured: every abs()-using module failed as postcondition until
    # `try unfold LemmaPy.PyAbs` — no earlier live case called abs).
    shadow = tmp_path / "shadow.py"
    shadow.write_text("#@ requires a >= 0\n"
                      "#@ ensures result == a\n"
                      "def PyAbs(a: int) -> int:\n"
                      "    return abs(a)\n")
    payload3 = verify_structured(shadow, tmp_path / "out3", backend="lean")
    assert payload3["status"] == "ok"


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_bool_predicates_verify(tmp_path):
    from lemmapy.agentio import verify_structured

    pred = tmp_path / "pos.py"
    pred.write_text("#@ ensures result == (x > 0)\n"
                    "def pos(x: int) -> bool:\n"
                    "    return x > 0\n")
    assert verify_structured(pred, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # Bool-literal branches exercise the ite-under-iff residue simp_all
    # normalizes (measured failing before the endgame extension).
    lit = tmp_path / "big.py"
    lit.write_text("#@ ensures result == (x >= 10)\n"
                   "def big(x: int) -> bool:\n"
                   "    if x >= 10:\n"
                   "        return True\n"
                   "    return False\n")
    assert verify_structured(lit, tmp_path / "o2",
                             backend="lean")["status"] == "ok"

    false_bool = tmp_path / "neg.py"
    false_bool.write_text("#@ ensures result == (x >= 0)\n"
                          "def neg(x: int) -> bool:\n"
                          "    return x > 0\n")
    payload = verify_structured(false_bool, tmp_path / "o3", backend="lean")
    assert payload["status"] == "failed"
    assert payload["failures"][0]["kind"] == "postcondition"


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_false_spec_fails_as_postcondition(tmp_path):
    from lemmapy.agentio import verify_structured

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == x + 2\n"
                   "def bump(x: int) -> int:\n"
                   "    return x + 1\n")
    payload = verify_structured(src, tmp_path / "out", backend="lean")
    assert payload["status"] == "failed"
    failure = payload["failures"][0]
    assert failure["kind"] == "postcondition"
    assert failure["py_line"] == 1  # the ensures clause, not Lean plumbing
