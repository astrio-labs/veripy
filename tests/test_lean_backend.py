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

    # NESTED quantifiers reusing the name must keep renaming past every
    # enclosing EMITTED binder (outer lands on f'', inner on f''' —
    # measured class: the inner binder landing on f'' captured the
    # outer one).
    nested = ("#@ requires f == 5\n"
              "#@ ensures forall f in range(0, 1) :: "
              "(forall f in range(0, 1) :: result >= f)\n"
              "def f(f: int) -> int:\n"
              "    return f\n")
    enc2 = _encode(nested)
    assert "∀ «f''» : Int" in enc2.lean_source
    assert "∀ «f'''» : Int" in enc2.lean_source
    # The inner body references the INNER binder (Python shadowing).
    assert "(«f» «f'») ≥ «f'''»" in enc2.lean_source


def test_shadowed_builtins_are_refused_not_mistranslated():
    # Soundness: Python calls the shadowing binding; translating to the
    # builtin would certify mathematical abs/min/max for a program that
    # never runs them.
    # Caught by the assigned-anywhere pre-scan (which also covers the
    # call-BEFORE-assign half Python treats as UnboundLocalError).
    local_shadow = ("#@ ensures result >= 0\n"
                    "def h(x: int) -> int:\n"
                    "    abs = x\n"
                    "    return abs(x)\n")
    with pytest.raises(EncodeError, match="cannot mean the builtin"):
        _encode(local_shadow)

    call_before_assign = ("#@ ensures result >= 0\n"
                          "def k(x: int) -> int:\n"
                          "    y = abs(x)\n"
                          "    abs = y\n"
                          "    return abs\n")
    with pytest.raises(EncodeError, match="cannot mean the builtin"):
        _encode(call_before_assign)

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

    # MODULE-LEVEL bindings (assignments, imports) could rebind a name
    # call sites translate as a builtin; the whole statement class is
    # rejected rather than the dangerous names enumerated. A leading
    # docstring stays legal.
    module_assign = ("abs = 5\n"
                     "#@ ensures result == x\n"
                     "def f(x: int) -> int:\n"
                     "    return x\n")
    with pytest.raises(EncodeError, match="module-level"):
        _encode(module_assign)

    module_import = ("import math\n"
                     "#@ ensures result == x\n"
                     "def f(x: int) -> int:\n"
                     "    return x\n")
    with pytest.raises(EncodeError, match="module-level"):
        _encode(module_import)

    with_docstring = ('"""A module docstring stays legal."""\n'
                      "#@ ensures result == x + 1\n"
                      "def bump(x: int) -> int:\n"
                      "    return x + 1\n")
    enc = _encode(with_docstring)  # must not raise
    assert "def «bump»" in enc.lean_source


def test_nested_spec_cannot_borrow_a_module_level_body():
    # A spec'd NESTED def sharing a name with an unspecified module-level
    # function paired by name alone — Lean would prove the module-level
    # body against the nested contract. The def line is now part of the
    # pairing key.
    nested = ("def outer(x: int) -> int:\n"
              "    #@ ensures result == y + 1\n"
              "    def g(y: int) -> int:\n"
              "        return y + 1\n"
              "    return x\n"
              "\n"
              "def g(y: int) -> int:\n"
              "    return y\n")
    with pytest.raises(EncodeError, match="nested"):
        _encode(nested)


def test_decorated_functions_are_refused():
    # A decorator can replace the callable; proving fn.body would
    # certify a contract for a function Python never runs.
    decorated = ("#@ ensures result == x\n"
                 "@staticmethod\n"
                 "def f(x: int) -> int:\n"
                 "    return x\n")
    with pytest.raises(EncodeError, match="decorat"):
        _encode(decorated)


ADDN = ("#@ requires n >= 0\n"
        "#@ ensures result == a + n\n"
        "def addn(n: int, a: int) -> int:\n"
        "    s = a\n"
        "    for i in range(n):\n"
        "        #@ invariant s == a + i\n"
        "        s = s + 1\n"
        "    return s\n")


def test_loop_emits_fuel_recursion_and_invariant_theorem():
    # P2 slice 1: for-range accumulator loops compile to fuel recursion
    # on Nat (structurally terminating — no termination_by), the
    # invariant becomes a generated Prop, and the induction theorem's
    # inductive step IS the invariant-preservation VC.
    enc = _encode(ADDN)
    assert ("def «addn_loop» («n» : Int) («a» : Int) : "
            "Nat → Int → Int → Int") in enc.lean_source
    assert "| (m + 1), «i», «s» =>" in enc.lean_source
    assert "def «addn_inv»" in enc.lean_source
    assert "theorem «addn_loop_inv»" in enc.lean_source
    assert "induction m with" in enc.lean_source
    # The main def threads the loop result; the spec theorem
    # instantiates the induction theorem and rewrites the fuel cast.
    assert "(«n»).toNat 0 «a»" in enc.lean_source
    assert "Int.toNat_of_nonneg" in enc.lean_source


def test_executable_old_is_refused_not_erased():
    # `old` exists only in spec clauses; in executable Python it is a
    # NameError at runtime, so the spec-context erasure (old(x) -> x)
    # would certify a function whose execution cannot happen. Every
    # executable position refuses: loop-free bodies, if-conditions, and
    # the loop pipeline's init/bound/step/return.
    for src in (
        # loop-free return
        "#@ ensures result == x\ndef f(x: int) -> int:\n"
        "    return old(x)\n",
        # local initializer
        "#@ ensures result == x\ndef f(x: int) -> int:\n"
        "    y = old(x)\n    return y\n",
        # if condition
        "#@ ensures result >= 0\ndef f(x: int) -> int:\n"
        "    if old(x) > 0:\n        return x\n    return 0\n",
        # loop step
        "#@ requires n >= 0\n#@ ensures result == n\n"
        "def f(n: int) -> int:\n    s = 0\n"
        "    for i in range(n):\n        #@ invariant s == i\n"
        "        s = s + old(n) - n + 1\n    return s\n",
        # loop return
        "#@ requires n >= 0\n#@ ensures result == n\n"
        "def f(n: int) -> int:\n    s = 0\n"
        "    for i in range(n):\n        #@ invariant s == i\n"
        "        s = s + 1\n    return old(s)\n",
    ):
        with pytest.raises(EncodeError, match="only meaningful in spec"):
            _encode(src)

    # ...while `old` in an ensures clause stays legal.
    spec_old = ("#@ ensures result == old(x) + 1\n"
                "def bump(x: int) -> int:\n"
                "    return x + 1\n")
    enc = _encode(spec_old)
    assert "(«bump» «x») = («x» + 1)" in enc.lean_source


def test_loop_shape_rejections():
    base = ("#@ requires n >= 0\n#@ ensures result == n\n"
            "def f(n: int) -> int:\n")
    cases = [
        # not the acc/for/return shape
        (base + "    s = 0\n    t = 1\n    for i in range(n):\n"
                "        #@ invariant s == i\n        s = s + 1\n"
                "    return s\n", "acc = init"),
        # iterating something other than range(<bound>)
        (base + "    s = 0\n    for i in range(0, n):\n"
                "        #@ invariant s == i\n        s = s + 1\n"
                "    return s\n", "range"),
        # loop body must be a single accumulator assignment
        (base + "    s = 0\n    for i in range(n):\n"
                "        #@ invariant s == i\n        s = s + 1\n"
                "        t = s\n    return s\n", "single assignment"),
        # the post-loop index value is a CPython artifact
        (base + "    s = 0\n    for i in range(n):\n"
                "        #@ invariant s == i\n        s = s + 1\n"
                "    return i\n", "loop index"),
        # exactly one invariant
        (base + "    s = 0\n    for i in range(n):\n"
                "        s = s + 1\n    return s\n", "invariant"),
    ]
    for src, needle in cases:
        with pytest.raises(EncodeError, match=needle):
            _encode(src)

    boolloop = ("#@ requires n >= 0\n#@ ensures result == (n >= 0)\n"
                "def g(n: int) -> bool:\n"
                "    s = 0\n"
                "    for i in range(n):\n"
                "        #@ invariant s == i\n"
                "        s = s + 1\n"
                "    return s >= 0\n")
    with pytest.raises(EncodeError, match="return `int`"):
        _encode(boolloop)


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_loops_verify_and_false_invariants_fail(tmp_path):
    from lemmapy.agentio import verify_structured

    src = tmp_path / "addn.py"
    src.write_text(ADDN)
    payload = verify_structured(src, tmp_path / "o1", backend="lean")
    assert payload["status"] == "ok"

    # A constant-init loop whose invariant SIMP-closes at i=0 (count:
    # 0 = 0): the generated inline proofs must be goal-guarded
    # (measured: unguarded push_cast after a closing simp errored
    # "No goals to be solved" and failed a true spec as unknown).
    cnt = tmp_path / "count.py"
    cnt.write_text("#@ requires n >= 0\n#@ ensures result == n\n"
                   "def count(n: int) -> int:\n"
                   "    s = 0\n"
                   "    for i in range(n):\n"
                   "        #@ invariant s == i\n"
                   "        s = s + 1\n"
                   "    return s\n")
    assert verify_structured(cnt, tmp_path / "o2",
                             backend="lean")["status"] == "ok"

    badinv = tmp_path / "badinv.py"
    badinv.write_text("#@ requires n >= 0\n#@ ensures result == a + n\n"
                      "def badinv(n: int, a: int) -> int:\n"
                      "    s = a\n"
                      "    for i in range(n):\n"
                      "        #@ invariant s == a\n"
                      "        s = s + 1\n"
                      "    return s\n")
    assert verify_structured(badinv, tmp_path / "o3",
                             backend="lean")["status"] == "failed"


SUM_LIST = ("#@ ensures result == sum(xs)\n"
            "def sum_list(xs: list[int]) -> int:\n"
            "    s = 0\n"
            "    for i in range(len(xs)):\n"
            "        #@ invariant s == sum(xs[:i])\n"
            "        s = s + xs[i]\n"
            "    return s\n")


def test_lists_emit_types_getd_take_and_pysum():
    # P2 slice 2: list[int] parameters, len/sum, structurally-safe
    # indexing (total getD where in-bounds is guaranteed by
    # construction), and xs[:i] prefix sums in invariants backed by the
    # prelude's PROVED PySum_take_succ lemma.
    enc = _encode(SUM_LIST)
    assert "def «sum_list_loop» («xs» : List Int)" in enc.lean_source
    assert "(«xs».getD («i»).toNat 0)" in enc.lean_source
    assert "LemmaPy.PySum («xs».take («i»).toNat)" in enc.lean_source
    assert "= (LemmaPy.PySum «xs»)" in enc.lean_source
    assert "theorem PySum_take_succ" in enc.lean_source  # prelude, proved


def test_quantifier_over_len_makes_its_binder_a_safe_index():
    # A binder over range(len(xs)) is guarded by its bound hypothesis
    # exactly where the body sits, so the body may index xs by it.
    src = ("#@ requires all(xs[k] >= 0 for k in range(len(xs)))\n"
           "#@ ensures result >= 0\n"
           "def size(xs: list[int]) -> int:\n"
           "    return len(xs)\n")
    enc = _encode(src)
    assert "(«xs».getD («k»).toNat 0) ≥ 0" in enc.lean_source
    assert "«k» < ((«xs».length : Int))" in enc.lean_source


def test_list_misuse_is_refused_not_mistranslated():
    loop = ("    s = 0\n"
            "    for i in range(len(xs)):\n"
            "        #@ invariant s == sum(xs[:i])\n"
            "        s = s + xs[i]\n"
            "    return s\n")
    cases = [
        # a list where an integer belongs
        ("#@ ensures result >= 0\ndef f(xs: list[int]) -> int:\n"
         "    return xs\n", "integer position"),
        # literal index: not structurally in bounds (xs could be empty)
        ("#@ ensures result >= 0\ndef f(xs: list[int]) -> int:\n"
         "    return xs[0]\n", "structurally in bounds"),
        # loop over range(n), not range(len(xs)): i is not a safe index
        ("#@ requires n >= 0\n#@ ensures result >= 0\n"
         "def f(xs: list[int], n: int) -> int:\n"
         "    s = 0\n"
         "    for i in range(n):\n"
         "        #@ invariant s >= 0\n"
         "        s = s + xs[i]\n"
         "    return s\n", "structurally in bounds"),
        # indexing a DIFFERENT list than the one bounding the loop
        ("#@ ensures result >= 0\n"
         "def f(xs: list[int], ys: list[int]) -> int:\n"
         "    s = 0\n"
         "    for i in range(len(xs)):\n"
         "        #@ invariant s >= 0\n"
         "        s = s + ys[i]\n"
         "    return s\n", "structurally in bounds"),
        # slices live inside sum(...) in invariants, nowhere else
        ("#@ ensures result >= 0\ndef f(xs: list[int]) -> int:\n"
         "    return xs[:1]\n", "inside an invariant"),
        # sum of a slice in the ENSURES: the loop index is out of
        # scope there, and an arbitrary bound may be negative (Python
        # clamps from the END for negative bounds; .toNat clamps to [])
        ("#@ ensures result == sum(xs[:n])\n"
         "def f(xs: list[int], n: int) -> int:\n" + loop,
         "loop index as the slice bound"),
        # len/sum apply to lists, not integers
        ("#@ ensures result == n\ndef f(n: int) -> int:\n"
         "    return len(n)\n", "list parameter only"),
        ("#@ ensures result == n\ndef f(n: int) -> int:\n"
         "    return sum(n)\n", "list parameter or"),
        # only list[int] element types have a model
        ("#@ ensures result >= 0\ndef f(xs: list[str]) -> int:\n"
         "    return 0\n", "must be `int` or `list"),
        # lists cannot be returned in this slice
        ("#@ ensures result == xs\ndef f(xs: list[int]) -> list[int]:\n"
         "    return xs\n", "return type"),
        # a quantifier binder shadowing a list parameter
        ("#@ ensures all(xs >= 0 for xs in range(n))\n"
         "def f(xs: list[int], n: int) -> int:\n"
         "    return 0\n", "shadows a list parameter"),
        # module-level defs named after the new builtins
        ("#@ ensures result >= 0\ndef sum(xs: list[int]) -> int:\n"
         "    return 0\n", "shadows an encoder builtin"),
        ("#@ ensures result >= 0\ndef len(xs: list[int]) -> int:\n"
         "    return 0\n", "shadows an encoder builtin"),
    ]
    for src, needle in cases:
        with pytest.raises(EncodeError, match=needle):
            _encode(src)


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_lists_verify(tmp_path):
    from lemmapy.agentio import verify_structured

    src = tmp_path / "sum_list.py"
    src.write_text(SUM_LIST)
    assert verify_structured(src, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # Offset accumulator: the invariant-preservation bridge
    # (toNat-successor rewrite + PySum_take_succ) is not shaped to
    # sum_list alone.
    plus = tmp_path / "sum_plus.py"
    plus.write_text("#@ ensures result == c + sum(xs)\n"
                    "def sum_plus(xs: list[int], c: int) -> int:\n"
                    "    s = c\n"
                    "    for i in range(len(xs)):\n"
                    "        #@ invariant s == c + sum(xs[:i])\n"
                    "        s = s + xs[i]\n"
                    "    return s\n")
    assert verify_structured(plus, tmp_path / "o2",
                             backend="lean")["status"] == "ok"

    # Loop-free list functions ride the same expression translator.
    flat = tmp_path / "flat.py"
    flat.write_text("#@ ensures result == sum(xs)\n"
                    "def total(xs: list[int]) -> int:\n"
                    "    return sum(xs)\n"
                    "\n"
                    "#@ ensures result == len(xs)\n"
                    "#@ ensures result >= 0\n"
                    "def size(xs: list[int]) -> int:\n"
                    "    return len(xs)\n")
    assert verify_structured(flat, tmp_path / "o3",
                             backend="lean")["status"] == "ok"

    # A wrong list spec still fails honestly as a prover verdict.
    bad = tmp_path / "bad.py"
    bad.write_text(SUM_LIST.replace("result == sum(xs)",
                                    "result == sum(xs) + 1"))
    payload = verify_structured(bad, tmp_path / "o4", backend="lean")
    assert payload["status"] == "failed"


def test_duplicate_defs_are_refused_not_mispaired():
    # Specs attach to the FIRST def, the name map keeps the LAST (and
    # CPython runs the last) — encoding would prove one body against
    # another definition's contract. Same refusal as the Dafny encoder.
    dup = ("#@ ensures result == x + 1\n"
           "def f(x: int) -> int:\n"
           "    return x + 1\n"
           "\n"
           "def f(x: int) -> int:\n"
           "    return x\n")
    with pytest.raises(EncodeError, match="duplicate definition"):
        _encode(dup)


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
