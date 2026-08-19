"""The Lean backend, slice 1: loop-free integer functions behind the
`ProofBackend` seam.

Split by dependency: encoder and classifier tests are pure Python (they
run everywhere, CI included); end-to-end tests need `lean` on PATH and
carry the house skipif. Every live assertion here was first pinned
against a real Lean 4.33 run.
"""

from pathlib import Path

import pytest

from veripy.backends.base import available_backends, get_backend
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.lean.backend import LeanBackend
from veripy.backends.lean.driver import classify_lean_message, find_lean
from veripy.backends.lean.encoder import encode_module_lean
from veripy.frontend.extract import parse_source

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
    # the prelude because call sites reference VeriPy.PyAbs qualified,
    # which no top-level def redeclares and no binder captures.
    shadows_prelude = ("#@ ensures result == abs(a)\n"
                       "def PyAbs(a: int) -> int:\n"
                       "    return abs(a)\n")
    enc2 = _encode(shadows_prelude)
    assert "def «PyAbs»" in enc2.lean_source          # user def, escaped
    assert "(VeriPy.PyAbs «a»)" in enc2.lean_source  # abs() -> qualified


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
    with pytest.raises(EncodeError, match="match its return type"):
        _encode(boolloop)


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_loops_verify_and_false_invariants_fail(tmp_path):
    from veripy.agentio import verify_structured

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
    assert "VeriPy.PySum («xs».take («i»).toNat)" in enc.lean_source
    assert "= (VeriPy.PySum «xs»)" in enc.lean_source
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
    from veripy.agentio import verify_structured

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


BELOW_T = ("#@ ensures result == all(xs[k] < t for k in range(len(xs)))\n"
           "def below_threshold(xs: list[int], t: int) -> bool:\n"
           "    b = True\n"
           "    for i in range(len(xs)):\n"
           "        #@ invariant b == all(xs[k] < t for k in range(i))\n"
           "        b = b and (xs[i] < t)\n"
           "    return b\n")

CONTAINS = ("#@ ensures result == any(xs[k] == v for k in range(len(xs)))\n"
            "def contains(xs: list[int], v: int) -> bool:\n"
            "    b = False\n"
            "    for i in range(len(xs)):\n"
            "        #@ invariant b == any(xs[k] == v for k in range(i))\n"
            "        b = b or (xs[i] == v)\n"
            "    return b\n")


def test_bool_loops_emit_bool_fuel_recursion_and_iff_invariant():
    # P2 slice 3: True/False-initialized accumulators with `and`/`or`
    # steps compile to Bool fuel recursion; the invariant's
    # `b == all(...)` rides the SAME Bool/Prop bridge as a bool
    # ensures ((b = true) ↔ ∀ ...), and the induction theorem's
    # inductive step is a generated constructor script that splits the
    # fresh index off the quantified prefix.
    enc = _encode(BELOW_T)
    assert ("def «below_threshold_loop» («xs» : List Int) («t» : Int) : "
            "Nat → Int → Bool → Bool") in enc.lean_source
    assert "(«b» && (decide" in enc.lean_source
    assert "((«b» = true) ↔ (∀ «k» : Int," in enc.lean_source
    assert "Bool.and_eq_true" in enc.lean_source
    assert "rintro ⟨hb, hlast⟩" in enc.lean_source

    enc2 = _encode(CONTAINS)
    assert "(«b» || (decide" in enc2.lean_source
    assert "((«b» = true) ↔ (∃ «k» : Int," in enc2.lean_source
    assert "Bool.or_eq_true" in enc2.lean_source
    # The invariant's binder domain is range(i) — the index PREFIX, in
    # bounds only as proof scaffolding (never executed), which is what
    # the scaffold mode of the list context licenses.
    assert "«k» < «i»" in enc2.lean_source


def test_bool_loop_misuse_is_refused():
    head = ("#@ ensures result == all(xs[k] < t for k in range(len(xs)))\n"
            "def f(xs: list[int], t: int) -> bool:\n")
    cases = [
        # step must be `acc and P` / `acc or P`
        (head + "    b = True\n    for i in range(len(xs)):\n"
                "        #@ invariant b == all(xs[k] < t for k in range(i))\n"
                "        b = xs[i] < t\n    return b\n",
         "updates as"),
        # the accumulator appears only as the left operand
        (head + "    b = True\n    for i in range(len(xs)):\n"
                "        #@ invariant b == all(xs[k] < t for k in range(i))\n"
                "        b = b and (b or xs[i] < t)\n    return b\n",
         "left operand"),
        # bool loops return the bare accumulator
        (head + "    b = True\n    for i in range(len(xs)):\n"
                "        #@ invariant b == all(xs[k] < t for k in range(i))\n"
                "        b = b and (xs[i] < t)\n    return b and True\n",
         "bare accumulator"),
        # a True-initialized accumulator in an int-returning function
        ("#@ ensures result >= 0\ndef f(xs: list[int]) -> int:\n"
         "    b = True\n    for i in range(len(xs)):\n"
         "        #@ invariant b == True\n"
         "        b = b and (xs[i] >= 0)\n    return b\n",
         "match its return type"),
        # `result` has no meaning in an invariant
        (head + "    b = True\n    for i in range(len(xs)):\n"
                "        #@ invariant result == True\n"
                "        b = b and (xs[i] < t)\n    return b\n",
         "only meaningful in `ensures`"),
        # a quantifier binder shadowing the accumulator would be
        # captured by the result substitution
        (head + "    b = True\n    for i in range(len(xs)):\n"
                "        #@ invariant b == all(b < t for b in range(i))\n"
                "        b = b and (xs[i] < t)\n    return b\n",
         "shadows the accumulator"),
    ]
    for src, needle in cases:
        with pytest.raises(EncodeError, match=needle):
            _encode(src)


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_bool_loops_verify(tmp_path):
    from veripy.agentio import verify_structured

    # The all-accumulator (below_threshold) and or-accumulator
    # (contains) classes both prove with the fixed cocktail. contains
    # is the first ∃-postcondition the backend PROVES: the invariant
    # induction carries the witness through the loop, where P1's fixed
    # script had none to offer.
    bt = tmp_path / "below_threshold.py"
    bt.write_text(BELOW_T)
    assert verify_structured(bt, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    ct = tmp_path / "contains.py"
    ct.write_text(CONTAINS)
    assert verify_structured(ct, tmp_path / "o2",
                             backend="lean")["status"] == "ok"

    # A wrong bool spec still fails honestly (>= in the ensures, < in
    # the loop).
    bad = tmp_path / "bad.py"
    bad.write_text(BELOW_T.replace("all(xs[k] < t for k in range(len(xs)))",
                                   "all(xs[k] >= t for k in range(len(xs)))"))
    assert verify_structured(bad, tmp_path / "o3",
                             backend="lean")["status"] == "failed"


EARLY_BT = ("#@ ensures result == "
            "all(l[k] < t for k in range(len(l)))\n"
            "def below_threshold(l: list[int], t: int) -> bool:\n"
            "    for i in range(len(l)):\n"
            "        #@ invariant all(l[k] < t for k in range(i))\n"
            "        if l[i] >= t:\n"
            "            return False\n"
            "    return True\n")


def test_early_return_loops_desugar_to_bool_accumulators():
    # The HumanEval search-loop shape: `if TEST: return False` inside
    # the loop desugars to the and-accumulator over not-TEST (return
    # True on hit is the or-accumulator over TEST). Result-faithful:
    # Python short-circuits, the fold runs on, and Bool and/or are
    # monotone over a pure body. The accumulator is synthesized fresh,
    # and the user's accumulator-free invariant becomes its iff-body.
    enc = _encode(EARLY_BT)
    assert "Nat → Int → Bool → Bool" in enc.lean_source
    assert "(«b» && (decide (¬(" in enc.lean_source     # not-TEST step
    assert "((«b» = true) ↔ (∀ «k» : Int," in enc.lean_source
    # The omega leaves bridge `l[i] >= t` against the invariant's
    # `l[k] < t` — same linear fact, different spelling.
    assert "first | exact hpi | omega" in enc.lean_source

    hit_true = ("#@ ensures result == "
                "any(l[k] == v for k in range(len(l)))\n"
                "def has(l: list[int], v: int) -> bool:\n"
                "    for i in range(len(l)):\n"
                "        #@ invariant all(l[k] != v for k in range(i))\n"
                "        if l[i] == v:\n"
                "            return True\n"
                "    return False\n")
    enc2 = _encode(hit_true)
    assert "(«b» || (decide ((" in enc2.lean_source     # TEST step

    # Non-literal returns and agreeing literals stay out.
    with pytest.raises(EncodeError, match="bool literals"):
        _encode(EARLY_BT.replace("return False", "return t > 0"))
    with pytest.raises(EncodeError, match="must differ"):
        _encode(EARLY_BT.replace("return True", "return False"))


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_early_return_loops_verify(tmp_path):
    from veripy.agentio import verify_structured

    # The frozen-corpus below_threshold (HumanEval/52) verbatim: the
    # first corpus task whose Lean column moved from encode-error to
    # proved by the early-return desugaring.
    src = tmp_path / "bt.py"
    src.write_text(EARLY_BT)
    assert verify_structured(src, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # The invariant states the wrong prefix property: fails honestly.
    bad = tmp_path / "bad.py"
    bad.write_text(EARLY_BT.replace("l[k] < t for k in range(i)",
                                    "l[k] > t for k in range(i)"))
    assert verify_structured(bad, tmp_path / "o2",
                             backend="lean")["status"] == "failed"


MAX_ELEMENT = ("#@ requires len(l) > 0\n"
               "#@ ensures exists i in range(len(l)) :: result == l[i]\n"
               "#@ ensures forall i in range(len(l)) :: l[i] <= result\n"
               "def max_element(l: list[int]) -> int:\n"
               "    m: int = l[0]\n"
               "    for i in range(len(l)):\n"
               "        #@ invariant forall k in range(i) :: l[k] <= m\n"
               "        #@ invariant exists k in range(len(l)) "
               ":: m == l[k]\n"
               "        if l[i] > m:\n"
               "            m = l[i]\n"
               "    return m\n")


def test_max_element_class_emits_min_max_and_witness_machinery():
    # P2 slice 5: conditional updates compile to max/min (omega-native,
    # no ite inside the loop atom), multiple invariants conjoin, the
    # literal init index is licensed by the requires length bound, and
    # the fuel-bound hypothesis (i + fuel ≤ N) rides the induction so
    # the ∃-witness survives the tail of the fold.
    enc = _encode(MAX_ELEMENT)
    assert "(max «m» («l».getD («i»).toNat 0))" in enc.lean_source
    assert "(«l».getD 0 0)" in enc.lean_source            # guarded l[0]
    assert "∧ (∃ «k» : Int," in enc.lean_source           # conjoined invs
    assert "+ (m' : Int) ≤" in enc.lean_source            # fuel bound,
    # freshened: the user accumulator is named m, so the machinery
    # binder steps aside instead of colliding («m» IS m).
    assert "by_cases hc :" in enc.lean_source             # witness step
    assert "have hi0" in enc.lean_source

    # An unguarded literal index refuses: no requires bound, no license.
    with pytest.raises(EncodeError, match="structurally in bounds"):
        _encode(MAX_ELEMENT.replace("#@ requires len(l) > 0\n", ""))

    # A conditional update that is not max/min-shaped refuses.
    with pytest.raises(EncodeError, match="max/min-shaped"):
        _encode(MAX_ELEMENT.replace("if l[i] > m:", "if l[i] > 0:"))


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_max_element_verifies(tmp_path):
    from veripy.agentio import verify_structured

    # The frozen-corpus max_element (HumanEval/35) shape verbatim.
    src = tmp_path / "max_element.py"
    src.write_text(MAX_ELEMENT)
    assert verify_structured(src, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # The min dual (mirrored guard) rides the same machinery.
    mn = tmp_path / "min_element.py"
    mn.write_text(MAX_ELEMENT
                  .replace("max_element", "min_element")
                  .replace("l[i] <= result", "l[i] >= result")
                  .replace("l[k] <= m", "l[k] >= m")
                  .replace("if l[i] > m:", "if l[i] < m:"))
    assert verify_structured(mn, tmp_path / "o2",
                             backend="lean")["status"] == "ok"

    # Flipping the guard against the invariant fails honestly.
    bad = tmp_path / "bad.py"
    bad.write_text(MAX_ELEMENT.replace("if l[i] > m:", "if l[i] < m:"))
    assert verify_structured(bad, tmp_path / "o3",
                             backend="lean")["status"] == "failed"


def test_invariants_must_sit_at_the_loop_head():
    # The Dafny backend's placement rule verbatim: strictly between the
    # `for` header and the first body statement. Multi-statement bodies
    # (early-return, conditional update) opened a span where an
    # invariant after an executable statement or inside a nested block
    # would otherwise be silently adopted — source the documented
    # fragment and the sibling backend refuse.
    inside_if = ("#@ ensures result == "
                 "all(l[k] < t for k in range(len(l)))\n"
                 "def f(l: list[int], t: int) -> bool:\n"
                 "    for i in range(len(l)):\n"
                 "        if l[i] >= t:\n"
                 "            #@ invariant all(l[k] < t for k in range(i))\n"
                 "            return False\n"
                 "    return True\n")
    with pytest.raises(EncodeError, match="top of the loop body"):
        _encode(inside_if)

    after_stmt = ("#@ requires len(l) > 0\n"
                  "#@ ensures forall i in range(len(l)) "
                  ":: l[i] <= result\n"
                  "def f(l: list[int]) -> int:\n"
                  "    m: int = l[0]\n"
                  "    for i in range(len(l)):\n"
                  "        if l[i] > m:\n"
                  "            m = l[i]\n"
                  "        #@ invariant forall k in range(i) :: l[k] <= m\n"
                  "    return m\n")
    with pytest.raises(EncodeError, match="top of the loop body"):
        _encode(after_stmt)

    # ...and an invariant in a loop-free function has no loop to claim
    # it: rejected, never silently dropped.
    no_loop = ("#@ ensures result == x\n"
               "def f(x: int) -> int:\n"
               "    #@ invariant x >= 0\n"
               "    return x\n")
    with pytest.raises(EncodeError, match="no loop"):
        _encode(no_loop)


def test_divmod_emits_python_semantics_not_lean_operators():
    # Python's `//`/`%` are FLOOR division and a divisor-signed remainder
    # (fdiv/fmod). Lean's own `/` and `%` are ediv/emod and differ on
    # negative divisors, so the encoder must never emit them directly.
    src = ("#@ requires p >= 2\n"
           "#@ ensures 0 <= result < p\n"
           "def mod_bound(a: int, p: int) -> int:\n"
           "    return a % p\n")
    enc = _encode(src)
    assert "(VeriPy.PyMod «a» «p»)" in enc.lean_source
    # The variable divisor's bounds are supplied explicitly: omega reasons
    # about `%` natively ONLY for constant divisors (measured).
    assert "VeriPy.PyMod_nonneg" in enc.lean_source
    assert "VeriPy.PyMod_lt" in enc.lean_source
    assert "have hdpos0 : (0:Int) < «p» := by omega" in enc.lean_source

    # A constant divisor DOES get bridged to `%`, which is what unlocks
    # omega's native arithmetic.
    half = ("#@ requires n >= 0\n#@ ensures result * 2 <= n\n"
            "def half(n: int) -> int:\n    return n // 2\n")
    assert "VeriPy.PyFloorDiv_pos" in _encode(half).lean_source


def test_divisor_wellformedness_is_discharged_not_assumed():
    # Python RAISES ZeroDivisionError on a zero divisor; Lean's fdiv/fmod
    # are total and return 0. A divisor that is not provably nonzero would
    # let Lean certify a program CPython cannot run, so it is refused.
    for src in (
        # no contract bound on the divisor at all
        "#@ ensures result >= 0\ndef f(a: int, b: int) -> int:\n"
        "    return a % b\n",
        # a literal zero divisor
        "#@ ensures result >= 0\ndef f(a: int) -> int:\n"
        "    return a // 0\n",
        # `p != 0` alone is not positivity, and this slice discharges the
        # obligation only via positivity (where the omega bridges apply)
        "#@ requires p != 0\n#@ ensures result >= 0\n"
        "def f(a: int, p: int) -> int:\n    return a % p\n",
        # the bound is under an `or`, so it is not a guarantee
        "#@ requires p > 0 or p < -5\n#@ ensures result >= 0\n"
        "def f(a: int, p: int) -> int:\n    return a % p\n",
    ):
        with pytest.raises(EncodeError, match="divisor"):
            _encode(src)

    # ...while a top-level requires conjunct proving positivity licenses it.
    ok = ("#@ requires p >= 2 and a >= 0\n#@ ensures 0 <= result < p\n"
          "def f(a: int, p: int) -> int:\n    return a % p\n")
    assert "VeriPy.PyMod" in _encode(ok).lean_source


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_divmod_model_matches_cpython_on_both_signs(tmp_path):
    # The differential fidelity rung for `//`/`%`: CPython computes the
    # expected values, Lean proves the prelude's model agrees. The negative
    # divisors are the point — the earlier design note claimed `Int.emod`
    # matched Python, and emod DOES agree whenever the divisor is positive,
    # so a positive-only suite would have ratified the wrong model.
    import subprocess

    from veripy.backends.lean.prelude import PRELUDE

    pairs = [(a, b) for a in (-7, -1, 0, 7) for b in (-3, -2, 2, 3)]

    def _suite(prelude: str, ps) -> str:
        lines = [prelude]
        for a, b in ps:
            lines.append(f"example : VeriPy.PyMod ({a} : Int) ({b}) "
                         f"= ({a % b}) := by rfl")
            lines.append(f"example : VeriPy.PyFloorDiv ({a} : Int) ({b}) "
                         f"= ({a // b}) := by rfl")
        return "\n".join(lines) + "\n"

    def _errors(text: str) -> int:
        path = tmp_path / "probe.lean"
        path.write_text(text)
        out = subprocess.run([str(find_lean()), str(path)],
                             capture_output=True, text=True)
        return out.stdout.count("error") + out.stderr.count("error")

    # The shipped model agrees with CPython everywhere.
    assert _errors(_suite(PRELUDE, pairs)) == 0

    # ...and the suite has TEETH: the ediv/emod model it rules out fails
    # here, but passes when restricted to positive divisors.
    wrong = ("namespace VeriPy\n"
             "def PyMod (a b : Int) : Int := Int.emod a b\n"
             "def PyFloorDiv (a b : Int) : Int := Int.ediv a b\n"
             "end VeriPy\n")
    assert _errors(_suite(wrong, pairs)) > 0
    assert _errors(_suite(wrong, [(a, b) for a, b in pairs if b > 0])) == 0


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_divmod_verifies(tmp_path):
    from veripy.agentio import verify_structured

    # Variable divisor: the bounds ride the prelude lemmas.
    mb = tmp_path / "mod_bound.py"
    mb.write_text("#@ requires p >= 2\n"
                  "#@ ensures 0 <= result < p\n"
                  "def mod_bound(a: int, p: int) -> int:\n"
                  "    return a % p\n")
    assert verify_structured(mb, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # Constant divisors: bridged, so omega does real arithmetic.
    par = tmp_path / "parity.py"
    par.write_text("#@ ensures result == (n % 2 == 0)\n"
                   "def is_even(n: int) -> bool:\n"
                   "    return n % 2 == 0\n"
                   "\n"
                   "#@ requires n >= 0\n"
                   "#@ ensures result * 2 <= n\n"
                   "#@ ensures n < result * 2 + 2\n"
                   "def half(n: int) -> int:\n"
                   "    return n // 2\n")
    assert verify_structured(par, tmp_path / "o2",
                             backend="lean")["status"] == "ok"

    # A false division spec still fails honestly.
    bad = tmp_path / "bad.py"
    bad.write_text("#@ requires p >= 2\n"
                   "#@ ensures result < p - 1\n"
                   "def f(a: int, p: int) -> int:\n"
                   "    return a % p\n")
    assert verify_structured(bad, tmp_path / "o3",
                             backend="lean")["status"] == "failed"


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_index_free_invariant_still_proves(tmp_path):
    from veripy.agentio import verify_structured

    # Regression: the fuel-cast rewrite was the one UNGUARDED step in the
    # generated script. An invariant that never mentions the loop index
    # leaves no `↑bound.toNat` in the instantiated hypothesis once the
    # invariant unfolds, so the rewrite failed and took a TRUE spec down
    # with it. Every generated step is guarded now.
    src = tmp_path / "grow.py"
    src.write_text("#@ requires n >= 0\n"
                   "#@ ensures result >= 0\n"
                   "def grow(n: int) -> int:\n"
                   "    c = 0\n"
                   "    for i in range(n):\n"
                   "        #@ invariant c >= 0\n"
                   "        c = c + 2\n"
                   "    return c\n")
    assert verify_structured(src, tmp_path / "o1",
                             backend="lean")["status"] == "ok"


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_division_inside_a_loop_verifies(tmp_path):
    from veripy.agentio import verify_structured

    # The loop machinery and the division machinery compose: the mod
    # bounds are supplied in LOOP context, where the induction theorem
    # carries the invariant but not the function's `requires` (so only
    # constant divisors qualify there).
    src = tmp_path / "count_mod.py"
    src.write_text("#@ requires n >= 0\n"
                   "#@ ensures result >= 0\n"
                   "def count_mod(n: int) -> int:\n"
                   "    c = 0\n"
                   "    for i in range(n):\n"
                   "        #@ invariant c >= 0\n"
                   "        c = c + i % 3\n"
                   "    return c\n")
    assert verify_structured(src, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # The divisor obligation is enforced inside the loop too, where the
    # theorem-level site scan cannot reach (it would read the loop index).
    bad = tmp_path / "bad.py"
    bad.write_text("#@ requires n >= 0\n"
                   "#@ ensures result >= 0\n"
                   "def f(n: int, d: int) -> int:\n"
                   "    c = 0\n"
                   "    for i in range(n):\n"
                   "        #@ invariant c >= 0\n"
                   "        c = c + i % d\n"
                   "    return c\n")
    with pytest.raises(EncodeError, match="divisor"):
        _encode(bad.read_text())


COUNTUP = ("#@ requires n >= 0\n"
           "#@ ensures result == n\n"
           "def countup(n: int) -> int:\n"
           "    c = 0\n"
           "    while c < n:\n"
           "        #@ invariant 0 <= c <= n\n"
           "        #@ decreases n - c\n"
           "        c = c + 1\n"
           "    return c\n")


def test_while_loops_emit_measure_machinery():
    # P2 slice 7: a `while` compiles to fuel recursion whose fuel is the
    # `#@ decreases` MEASURE rather than a range bound. The condition
    # becomes a Bool def (giving the `if` its Decidable instance and the
    # theorem a uniform way to say the condition is false at the end).
    enc = _encode(COUNTUP)
    assert "def «countup_cond» («n» : Int) («c» : Int) : Bool" in enc.lean_source
    assert "def «countup_meas» («n» : Int) («c» : Int) : Int" in enc.lean_source
    assert "def «countup_inv»" in enc.lean_source
    assert "def «countup_loop» («n» : Int) : Nat → Int → Int" in enc.lean_source
    # Concluding `cond = false` is what separates a loop that EXITED
    # from one that merely ran out of fuel.
    assert "= false := by" in enc.lean_source
    # The fuel at entry is the measure at entry.
    assert "(«countup_meas» «n» 0).toNat 0" in enc.lean_source


def test_while_shape_rejections():
    base = ("#@ requires n >= 0\n#@ ensures result == n\n"
            "def f(n: int) -> int:\n")
    cases = [
        # the measure is the fuel bound, so it is required
        (base + "    c = 0\n    while c < n:\n"
                "        #@ invariant 0 <= c <= n\n"
                "        c = c + 1\n    return c\n", "decreases"),
        # exactly one measure
        (base + "    c = 0\n    while c < n:\n"
                "        #@ invariant 0 <= c <= n\n"
                "        #@ decreases n - c\n"
                "        #@ decreases n\n"
                "        c = c + 1\n    return c\n", "decreases"),
        # the body is a single accumulator assignment
        (base + "    c = 0\n    while c < n:\n"
                "        #@ invariant 0 <= c <= n\n"
                "        #@ decreases n - c\n"
                "        c = c + 1\n        n = n\n"
                "    return c\n", "single assignment"),
        # acc = init; while ...; return expr
        (base + "    c = 0\n    d = 1\n    while c < n:\n"
                "        #@ invariant 0 <= c <= n\n"
                "        #@ decreases n - c\n"
                "        c = c + 1\n    return c\n", "must be exactly"),
        # bool accumulators stay out of the while slice
        ("#@ ensures result == True\ndef f(n: int) -> bool:\n"
         "    b = True\n    while b:\n"
         "        #@ invariant b == True\n"
         "        #@ decreases 0\n"
         "        b = b\n    return b\n", "bool accumulator"),
    ]
    for src, needle in cases:
        with pytest.raises(EncodeError, match=needle):
            _encode(src)

    # `decreases` on a for-range loop is meaningless: its fuel is the
    # range bound, so the clause would be silently ignored.
    forloop = ("#@ requires n >= 0\n#@ ensures result == n\n"
               "def f(n: int) -> int:\n    s = 0\n"
               "    for i in range(n):\n"
               "        #@ invariant s == i\n"
               "        #@ decreases n - i\n"
               "        s = s + 1\n    return s\n")
    with pytest.raises(EncodeError, match="only meaningful on a `while`"):
        _encode(forloop)


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_while_loops_verify(tmp_path):
    from veripy.agentio import verify_structured

    up = tmp_path / "countup.py"
    up.write_text(COUNTUP)
    assert verify_structured(up, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # A decreasing measure on a decreasing accumulator.
    down = tmp_path / "countdown.py"
    down.write_text("#@ requires n >= 0\n"
                    "#@ ensures result == 0\n"
                    "def countdown(n: int) -> int:\n"
                    "    c = n\n"
                    "    while c > 0:\n"
                    "        #@ invariant 0 <= c\n"
                    "        #@ decreases c\n"
                    "        c = c - 1\n"
                    "    return c\n")
    assert verify_structured(down, tmp_path / "o2",
                             backend="lean")["status"] == "ok"

    # SOUNDNESS: the measure does not actually decrease, so this loop
    # never terminates in Python. It must NOT verify — the fuel model
    # would otherwise certify a value the program never returns.
    spin = tmp_path / "spin.py"
    spin.write_text("#@ requires n >= 1\n"
                    "#@ ensures result == n\n"
                    "def spin(n: int) -> int:\n"
                    "    c = 0\n"
                    "    while c < n:\n"
                    "        #@ invariant 0 <= c <= n\n"
                    "        #@ decreases n - c\n"
                    "        c = c\n"
                    "    return c\n")
    assert verify_structured(spin, tmp_path / "o3",
                             backend="lean")["status"] == "failed"

    # A false postcondition still fails honestly.
    bad = tmp_path / "bad.py"
    bad.write_text(COUNTUP.replace("result == n", "result == n + 1"))
    assert verify_structured(bad, tmp_path / "o4",
                             backend="lean")["status"] == "failed"


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_squaring_while_loop_verifies_without_the_maximality_clause(tmp_path):
    from veripy.agentio import verify_structured

    # The corpus isqrt, minus its maximality clause. omega is LINEAR and
    # core Lean has no nlinarith, so the squaring obligations ride the
    # prelude's SqGeSelf (unconditional on Int, hence safe to hand omega
    # wherever a squared term appears).
    src = tmp_path / "isqrt.py"
    src.write_text("#@ requires n >= 0\n"
                   "#@ ensures result >= 0\n"
                   "#@ ensures result * result <= n\n"
                   "#@ ensures n < (result + 1) * (result + 1)\n"
                   "def isqrt(n: int) -> int:\n"
                   "    r = 0\n"
                   "    while (r + 1) * (r + 1) <= n:\n"
                   "        #@ invariant 0 <= r <= n\n"
                   "        #@ invariant r * r <= n\n"
                   "        #@ decreases n - r\n"
                   "        r = r + 1\n"
                   "    return r\n")
    assert verify_structured(src, tmp_path / "o1",
                             backend="lean")["status"] == "ok"

    # The maximality clause is the one that does NOT come free here: it
    # needs squaring MONOTONICITY under a quantifier, which no fixed
    # linear script supplies. Dafny gets it from Z3's nonlinear
    # arithmetic; in Lean it waits for the sidecar channel (P3). Pinned
    # so the day it starts passing is noticed.
    full = tmp_path / "isqrt_full.py"
    full.write_text(src.read_text().replace(
        "def isqrt(n: int) -> int:",
        "#@ ensures forall k in range(0, n + 1) :: k * k > n or k <= result\n"
        "def isqrt(n: int) -> int:"))
    assert verify_structured(full, tmp_path / "o2",
                             backend="lean")["status"] == "failed"


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
    import veripy.backends.lean.driver as driver_mod

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
    from veripy.agentio import verify_structured

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
    # `try unfold VeriPy.PyAbs` — no earlier live case called abs).
    shadow = tmp_path / "shadow.py"
    shadow.write_text("#@ requires a >= 0\n"
                      "#@ ensures result == a\n"
                      "def PyAbs(a: int) -> int:\n"
                      "    return abs(a)\n")
    payload3 = verify_structured(shadow, tmp_path / "out3", backend="lean")
    assert payload3["status"] == "ok"


@pytest.mark.skipif(find_lean() is None, reason="lean not installed")
def test_end_to_end_bool_predicates_verify(tmp_path):
    from veripy.agentio import verify_structured

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
    from veripy.agentio import verify_structured

    src = tmp_path / "m.py"
    src.write_text("#@ ensures result == x + 2\n"
                   "def bump(x: int) -> int:\n"
                   "    return x + 1\n")
    payload = verify_structured(src, tmp_path / "out", backend="lean")
    assert payload["status"] == "failed"
    failure = payload["failures"][0]
    assert failure["kind"] == "postcondition"
    assert failure["py_line"] == 1  # the ensures clause, not Lean plumbing


def test_lean_rejects_break_and_continue_loudly():
    # The Dafny backend admits these; Lean's fuel-recursion lowering has
    # no continue that still advances the index, so they must fail here
    # rather than verify vacuously.
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result >= 0\n"
        "def f(n: int) -> int:\n"
        "    s = 0\n"
        "    for i in range(n):\n"
        "        #@ invariant s >= 0\n"
        "        continue\n"
        "        s = s + 1\n"
        "    return s\n"
    )
    with pytest.raises(EncodeError, match="break/continue are outside the Lean slice"):
        _encode(src)


def test_lean_rejects_tuple_types_loudly():
    src = (
        "#@ ensures result[0] == x\n"
        "def pair(x: int, y: int) -> tuple[int, int]:\n"
        "    return (x, y)\n"
    )
    with pytest.raises(EncodeError, match="tuple types are outside the Lean slice"):
        _encode(src)


def test_lean_rejects_tuple_params_loudly():
    src = (
        "#@ ensures result == p[0]\n"
        "def fst(p: tuple[int, int]) -> int:\n"
        "    return p[0]\n"
    )
    with pytest.raises(EncodeError, match="tuple types are outside the Lean slice"):
        _encode(src)


def test_lean_rejects_all_in_a_bool_body():
    # Dafny admits `return all(...)` as forall; wrapping that Prop in
    # `decide` has no Decidable instance on unbounded Int.
    src = (
        "#@ requires n >= 0\n"
        "#@ ensures result == True\n"
        "def f(n: int) -> bool:\n"
        "    return all(i >= 0 for i in range(n))\n"
    )
    with pytest.raises(EncodeError, match="all/any in a bool-returning body"):
        _encode(src)


def test_lean_rejects_filtered_all_loudly():
    src = (
        "#@ ensures result == True or result == False\n"
        "def f(n: int) -> bool:\n"
        "    return all(i > 0 for i in range(n) if i % 2 == 0)\n"
    )
    with pytest.raises(EncodeError, match="filtered quantifiers are outside the Lean slice"):
        _encode(src)


def test_lean_rejects_foreach_unpack_loudly():
    src = (
        "#@ ensures result >= 0 or result < 0\n"
        "def f(n: int) -> int:\n"
        "    s = 0\n"
        "    for a, b in range(n):\n"
        "        s = s + 1\n"
        "    return s\n"
    )
    with pytest.raises(EncodeError, match="destructuring loop targets are outside the Lean slice"):
        _encode(src)
