"""The Lean 4 prelude: Python semantics, pinned.

Slice 1 needs almost nothing — `min`/`max` on `Int` and `omega` are core
Lean — so the prelude is deliberately tiny and the artifact needs NO lake
project and NO external dependencies: bare `lean --json file.lean`
elaborates against core, which kills the build-latency risk the ROADMAP
flagged for the repair loop.

Every definition here must match CPython on the shared domain, and the
match is pinned by the cross-backend differential fidelity tests (the R5
rung, extended to Lean in this track). Versioned like the Dafny preamble:
provenance rides every payload, and two "ok" verdicts must be comparable.
"""

PRELUDE_VERSION = "lean-0.7"

# The prelude lives in its own namespace and every call site references
# it QUALIFIED (VeriPy.PyAbs). Escaping user identifiers handles
# keywords, but «PyAbs» IS the identifier PyAbs (guillemets quote, they
# do not namespace — measured: a module `def PyAbs` failed with
# "`PyAbs` has already been declared"), so separation from user names
# has to come from the namespace: a top-level user def cannot redeclare
# a namespaced name, and a binder cannot capture a qualified reference.
#
# PySum models Python's `sum` on `list[int]` (Python folds left, PySum
# folds right; Int addition is commutative and associative, so the
# values agree). PySum_take_succ is the lemma pack behind sum-loop
# invariants: it peels the (n+1)-prefix sum into the n-prefix sum plus
# the element, which is the invariant-preservation step. It is PROVED
# here, not assumed — the prelude carries no axioms, and P3's
# `#print axioms` checker will pin that.
PRELUDE = """\
-- veripy Lean prelude {version} (loop-free, for-range loops, lists, //, %)
-- Python semantics on Int. Every def must match CPython on the shared
-- domain; the differential fidelity suite pins the correspondence.

namespace VeriPy

def PyAbs (a : Int) : Int := if a < 0 then -a else a

def PySum : List Int → Int
  | [] => 0
  | x :: rest => x + PySum rest

-- Python's `//` and `%` are FLOOR division and a remainder that takes the
-- sign of the DIVISOR: fdiv/fmod, not ediv/emod (Lean's own `/` and `%`).
-- Measured against CPython on both signs of both operands:
--   -7 // 3 = -3, 7 // -3 = -3, -7 % 3 = 2, 7 % -3 = -2.
-- emod agrees only when the divisor is positive, so a positive-divisor-only
-- test suite would never catch the difference. The differential suite pins
-- all four sign combinations.
def PyFloorDiv (a b : Int) : Int := Int.fdiv a b

def PyMod (a b : Int) : Int := Int.fmod a b

-- Bridges to Lean's own `/` and `%`, which omega reasons about NATIVELY
-- for constant divisors. Without these every division goal is an opaque
-- atom (measured).
theorem PyMod_pos (a b : Int) (h : 0 < b) : PyMod a b = a % b := by
  unfold PyMod
  rw [Int.fmod_eq_emod]
  simp [show (0:Int) ≤ b from by omega]

theorem PyFloorDiv_pos (a b : Int) (h : 0 < b) : PyFloorDiv a b = a / b := by
  unfold PyFloorDiv
  rw [Int.fdiv_eq_ediv]
  simp [show (0:Int) ≤ b from by omega]

-- omega handles `%` only for CONSTANT divisors, so a variable-divisor
-- bound (the `0 <= result < p` postcondition class) needs these supplied.
theorem PyMod_nonneg (a b : Int) (h : 0 < b) : 0 ≤ PyMod a b := by
  rw [PyMod_pos _ _ h]; exact Int.emod_nonneg a (by omega)

theorem PyMod_lt (a b : Int) (h : 0 < b) : PyMod a b < b := by
  rw [PyMod_pos _ _ h]; exact Int.emod_lt_of_pos a h

-- omega is LINEAR, and core Lean has no nlinarith, so a squaring loop
-- (isqrt) stalls on facts like `n < (n+1)*(n+1)`. This one lemma
-- supplies the missing link, and it holds for EVERY integer: a <= 0
-- gives a <= 0 <= a*a, and a >= 1 gives a*a >= a*1. Being
-- hypothesis-free, it can be handed to omega unconditionally wherever a
-- squared term appears, with no side goal to discharge and no risk of
-- breaking a proof that did not need it.
-- Python's `**` on ints, for a NON-NEGATIVE exponent. A negative
-- exponent makes CPython return a FLOAT, which is outside the int
-- fragment, so the encoder discharges e >= 0 as a well-formedness
-- obligation exactly as it does for a divisor. Checked against CPython
-- on both signs of the base: 2**5 = 32, (-2)**3 = -8, (-2)**4 = 16.
def PyPow (a : Int) (e : Int) : Int := a ^ e.toNat

theorem PyPow_zero (a : Int) : PyPow a 0 = 1 := by
  unfold PyPow; simp

theorem PyPow_succ (a : Int) (e : Int) (h : 0 ≤ e) :
    PyPow a (e + 1) = PyPow a e * a := by
  unfold PyPow
  rw [show (e + 1).toNat = e.toNat + 1 from by omega, Int.pow_succ]

-- Exit-state endgames instantiate an invariant's quantifier at the
-- RESULT, which surfaces self and zero residues: gcd's divisor set at
-- d = x contains `x % x` and (after the exit condition) `0 % x`.
theorem PyMod_self (a : Int) : PyMod a a = 0 := Int.fmod_self

theorem PyMod_zero_left (b : Int) : PyMod 0 b = 0 := Int.zero_fmod b

theorem SqGeSelf (a : Int) : a ≤ a * a := by
  rcases Int.lt_or_le a 1 with h | h
  · have hn : 0 ≤ (-a) * (-a) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.neg_mul_neg] at hn
    omega
  · calc a = a * 1 := by omega
      _ ≤ a * a := Int.mul_le_mul_of_nonneg_left h (by omega)

theorem PySum_take_succ (xs : List Int) (n : Nat) :
    PySum (xs.take (n + 1)) = PySum (xs.take n) + xs.getD n 0 := by
  induction xs generalizing n with
  | nil => simp [PySum, List.getD]
  | cons a rest ih =>
    cases n with
    | zero => simp [PySum, List.getD]
    | succ m =>
      simp only [List.take_succ_cons, PySum, List.getD_cons_succ, ih m]
      omega

end VeriPy
""".format(version=PRELUDE_VERSION)

# Line count the prelude prepends before the first encoded definition —
# the encoder's line_map starts after it.
PRELUDE_LINES = PRELUDE.count("\n")
