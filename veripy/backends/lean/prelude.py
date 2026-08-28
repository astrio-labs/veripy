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

PRELUDE_VERSION = "lean-0.15"

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

-- Decidability of range-bounded ∃, by recursion on the WIDTH. This
-- is what lets a nested pure search flatten into a single fold whose
-- test is `decide (∃ ...)` -- and it composes, so a triple loop
-- flattens the same way (nested ∃ of nested ∃ stays decidable).
def IntBexWitness (P : Int → Prop) [DecidablePred P]
    (lo : Int) : Nat → Bool
  | 0 => false
  | (w + 1) => decide (P lo) || IntBexWitness P (lo + 1) w

theorem IntBexWitness_iff (P : Int → Prop) [DecidablePred P]
    (lo : Int) (w : Nat) :
    IntBexWitness P lo w = true ↔
      ∃ b : Int, (lo ≤ b ∧ b < lo + w) ∧ P b := by
  induction w generalizing lo with
  | zero =>
    simp [IntBexWitness]
    intro b h1 h2
    omega
  | succ k ih =>
    simp only [IntBexWitness, Bool.or_eq_true, decide_eq_true_eq,
               ih (lo + 1)]
    constructor
    · rintro (hp | ⟨b, hb, hpb⟩)
      · exact ⟨lo, ⟨by omega, by omega⟩, hp⟩
      · exact ⟨b, ⟨by omega, by omega⟩, hpb⟩
    · rintro ⟨b, ⟨hb1, hb2⟩, hpb⟩
      rcases Classical.em (b = lo) with he | hne
      · left; rw [← he]; exact hpb
      · right; exact ⟨b, ⟨by omega, by omega⟩, hpb⟩

instance IntBexDec (P : Int → Prop) [DecidablePred P] (lo hi : Int) :
    Decidable (∃ b : Int, (lo ≤ b ∧ b < hi) ∧ P b) :=
  decidable_of_iff
    (IntBexWitness P lo (hi - lo).toNat = true)
    (by rw [IntBexWitness_iff]
        constructor
        · rintro ⟨b, ⟨h1, h2⟩, hp⟩
          exact ⟨b, ⟨h1, by omega⟩, hp⟩
        · rintro ⟨b, ⟨h1, h2⟩, hp⟩
          exact ⟨b, ⟨h1, by omega⟩, hp⟩)

-- Counting survives a filter the counted element passes: the spine of
-- the filtered-comprehension class (`[x for x in l if P]` preserves
-- multiplicity of every element satisfying P).
theorem Count_filter_of_pos (p : Int → Bool) (a : Int) (l : List Int)
    (h : p a = true) : (l.filter p).count a = l.count a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p x = true
    · simp [hx, List.count_cons, ih]
    · have hxa : ¬(x = a) := fun he => hx (he ▸ h)
      simp [hx, ih, hxa]

-- sorted(list(set(l))): insertion sort that DROPS duplicates,
-- so strict adjacency, and both membership directions, fall to
-- structural induction (core's eraseDups hides an accumulator
-- that resists induction; mergeSort would still owe the
-- nodup-to-strict step).
def InsertUnique (a : Int) : List Int → List Int
  | [] => [a]
  | b :: bs =>
      if a < b then a :: b :: bs
      else if a = b then b :: bs
      else b :: InsertUnique a bs

def SortedUnique : List Int → List Int
  | [] => []
  | x :: xs => InsertUnique x (SortedUnique xs)

theorem Mem_InsertUnique (x a : Int) (l : List Int) :
    x ∈ InsertUnique a l ↔ (x = a ∨ x ∈ l) := by
  induction l with
  | nil => simp [InsertUnique]
  | cons b bs ih =>
    by_cases h1 : a < b
    · simp [InsertUnique, h1]
    · by_cases h2 : a = b
      · subst h2
        simp [InsertUnique, h1, List.mem_cons]
      · simp only [InsertUnique, if_neg h1, if_neg h2,
                   List.mem_cons, ih]
        constructor
        · rintro (h | h)
          · exact Or.inr (Or.inl h)
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
        · rintro (h | h)
          · exact Or.inr (Or.inl h)
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)

theorem Mem_SortedUnique (x : Int) (l : List Int) :
    x ∈ SortedUnique l ↔ x ∈ l := by
  induction l with
  | nil => simp [SortedUnique]
  | cons y ys ih => simp [SortedUnique, Mem_InsertUnique, ih]

theorem Pairwise_InsertUnique (a : Int) (l : List Int)
    (h : List.Pairwise (· < ·) l) :
    List.Pairwise (· < ·) (InsertUnique a l) := by
  induction l with
  | nil => simp [InsertUnique]
  | cons b bs ih =>
    rcases List.pairwise_cons.mp h with ⟨hb, hbs⟩
    by_cases h1 : a < b
    · simp only [InsertUnique, if_pos h1]
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro y hy
      rcases List.mem_cons.mp hy with h' | h'
      · omega
      · have := hb y h'
        omega
    · by_cases h2 : a = b
      · subst h2
        simpa [InsertUnique, h1] using h
      · simp only [InsertUnique, if_neg h1, if_neg h2]
        refine List.pairwise_cons.mpr ⟨?_, ih hbs⟩
        intro y hy
        rcases (Mem_InsertUnique y a bs).mp hy with h' | h'
        · omega
        · exact hb y h'

theorem Pairwise_SortedUnique (l : List Int) :
    List.Pairwise (· < ·) (SortedUnique l) := by
  induction l with
  | nil => simp [SortedUnique]
  | cons y ys ih => exact Pairwise_InsertUnique y (SortedUnique ys) ih

theorem Pairwise_getD_lt (l : List Int) (i : Int)
    (hp : List.Pairwise (· < ·) l)
    (h0 : 0 ≤ i) (h1 : i + 1 < (l.length : Int)) :
    l.getD i.toNat 0 < l.getD (i + 1).toNat 0 := by
  induction l generalizing i with
  | nil => simp at h1; omega
  | cons x xs ih =>
    rcases List.pairwise_cons.mp hp with ⟨hx, hxs⟩
    by_cases hz : i = 0
    · subst hz
      have hne : xs ≠ [] := by
        intro he; subst he; simp at h1
      simp only [Int.toNat_zero, List.getD_cons_zero]
      have : (0 + 1 : Int).toNat = 1 := rfl
      rw [this]
      have hmem : xs.getD 0 0 ∈ xs := by
        cases xs with
        | nil => exact absurd rfl hne
        | cons z zs => simp
      exact hx _ (by simpa using hmem)
    · have hpos : 0 < i := by omega
      have e1 : i.toNat = (i - 1).toNat + 1 := by omega
      have e2 : (i + 1).toNat = ((i - 1) + 1).toNat + 1 := by omega
      rw [e1, e2, List.getD_cons_succ, List.getD_cons_succ]
      exact ih (i - 1) hxs (by omega) (by simp at h1 ⊢; omega)

-- The three spec-shaped corollaries the ladder instantiates.
theorem SortedUnique_adjacent (l : List Int) (i : Int)
    (h0 : 0 ≤ i) (h1 : i + 1 < ((SortedUnique l).length : Int)) :
    (SortedUnique l).getD i.toNat 0 < (SortedUnique l).getD (i + 1).toNat 0 :=
  Pairwise_getD_lt _ _ (Pairwise_SortedUnique l) h0 h1

theorem SortedUnique_getD_mem_src (l : List Int) (i : Int)
    (h0 : 0 ≤ i) (h1 : i < ((SortedUnique l).length : Int)) :
    (SortedUnique l).getD i.toNat 0 ∈ l := by
  have : (SortedUnique l).getD i.toNat 0 ∈ SortedUnique l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  exact (Mem_SortedUnique _ l).mp this

theorem GetD_mem_SortedUnique (l : List Int) (i : Int)
    (h0 : 0 ≤ i) (h1 : i < (l.length : Int)) :
    l.getD i.toNat 0 ∈ SortedUnique l := by
  refine (Mem_SortedUnique _ l).mpr ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

-- Squaring is monotone on the nonnegatives: what Z3 applies natively
-- for the isqrt-class maximality post ("no k in range beats the
-- answer"), spelled once so the fixed while-endgame has the move.
theorem SqLeSq (a b : Int) (h0 : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h h h0 (Int.le_trans h0 h)

-- A square is nonnegative, and so is a sum of squares: what Z3 knows
-- natively for the sum_squares-class `result >= 0` post. Core Lean has
-- no `positivity`, so both are spelled once.
theorem SqNonNeg (x : Int) : 0 ≤ x * x := by
  rcases Classical.em (0 ≤ x) with h | h
  · exact Int.mul_nonneg h h
  · have h2 : 0 ≤ -x := by omega
    have h3 := Int.mul_nonneg h2 h2
    have h4 : (-x) * (-x) = x * x := Int.neg_mul_neg x x
    omega

theorem PySum_sq_nonneg (l : List Int) :
    0 ≤ PySum (l.map (fun x => x * x)) := by
  induction l with
  | nil => simp [PySum]
  | cons x xs ih =>
    simp only [List.map_cons, PySum]
    have hx := SqNonNeg x
    omega

theorem SqGeSelf (a : Int) : a ≤ a * a := by
  rcases Int.lt_or_le a 1 with h | h
  · have hn : 0 ≤ (-a) * (-a) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.neg_mul_neg] at hn
    omega
  · calc a = a * 1 := by omega
      _ ≤ a * a := Int.mul_le_mul_of_nonneg_left h (by omega)

-- The mapped-fold pair (mbpp_sum_squares class). The slice-extension
-- assert `[f(x) for x in xs[:i+1]] == [f(x) for x in xs[:i]] + [f(xs[i])]`
-- is proved by Map_take_succ (its bound comes from the obligation's own
-- `i < len` hypothesis), and the proved form then steps the invariant
-- through PySum_append_one -- hypothesis-free, so it can sit in the
-- preservation simp set unconditionally.
-- The UNMAPPED slice extension (below_zero class): the same hint as
-- Map_take_succ with no comprehension around it.
theorem Take_succ_getD (xs : List Int) (n : Nat) (h : n < xs.length) :
    xs.take (n + 1) = xs.take n ++ [xs.getD n 0] := by
  induction xs generalizing n with
  | nil => simp at h
  | cons x rest ih =>
    cases n with
    | zero => simp [List.getD]
    | succ m =>
      simp only [List.take_succ_cons, List.getD_cons_succ]
      rw [ih m (by simpa using h)]
      simp

-- Reading an element through a trailing append (intersperse class):
-- inside the old prefix it is the old element, at the seam it is the
-- appended one.
theorem GetD_append_left (xs : List Int) (a : Int) (k : Nat)
    (h : k < xs.length) :
    (xs ++ [a]).getD k 0 = xs.getD k 0 := by
  induction xs generalizing k with
  | nil => simp at h
  | cons x rest ih =>
    cases k with
    | zero => simp [List.getD]
    | succ m =>
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih m (by simpa using h)

theorem GetD_append_last (xs : List Int) (a : Int) :
    (xs ++ [a]).getD xs.length 0 = a := by
  induction xs with
  | nil => simp [List.getD]
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons,
               List.getD_cons_succ]
    exact ih

theorem PySum_append_one (xs : List Int) (a : Int) :
    PySum (xs ++ [a]) = PySum xs + a := by
  induction xs with
  | nil => simp [PySum]
  | cons x rest ih => simp [PySum, ih]; omega

theorem Map_take_succ (f : Int → Int) (xs : List Int) (n : Nat)
    (h : n < xs.length) :
    (xs.take (n + 1)).map f = (xs.take n).map f ++ [f (xs.getD n 0)] := by
  induction xs generalizing n with
  | nil => simp at h
  | cons x rest ih =>
    cases n with
    | zero => simp [List.getD]
    | succ m =>
      simp only [List.take_succ_cons, List.map_cons, List.getD_cons_succ]
      rw [ih m (by simpa using h)]
      simp

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

-- max over a list: head-seeded foldl, [] totalized to 0 (Python's
-- max([]) raises, so every use site owes a nonemptiness story — the
-- rolling_max class only ever applies it to nonempty prefixes).
def ListMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

theorem Foldl_max_append_one (a : Int) (xs : List Int) (y : Int) :
    (xs ++ [y]).foldl max a = max (xs.foldl max a) y := by
  induction xs generalizing a with
  | nil => rfl
  | cons z zs ih => simp [List.foldl_cons, ih]

theorem ListMax_append_one (xs : List Int) (y : Int) (h : xs ≠ []) :
    ListMax (xs ++ [y]) = max (ListMax xs) y := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x rest =>
    simp only [ListMax, List.cons_append]
    exact Foldl_max_append_one x rest y

theorem ListMax_take_one (l : List Int) (h : l ≠ []) :
    ListMax (l.take 1) = l.getD 0 0 := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem ListMax_take_succ (l : List Int) (n : Nat)
    (h1 : 1 ≤ n) (h2 : n < l.length) :
    ListMax (l.take (n + 1)) = max (ListMax (l.take n)) (l.getD n 0) := by
  rw [Take_succ_getD l n h2]
  apply ListMax_append_one
  intro he
  have hlen : (l.take n).length = n := by
    simp [List.length_take]; omega
  rw [he] at hlen
  simp at hlen
  omega

-- ListMax dominates every member of the list — the rolling_max
-- domination post (`numbers[j] <= result[i]` for j ≤ i) reduces to
-- membership of the prefix. Seed and member dominance are spelled for
-- the head-seeded foldl, then getD-of-take membership connects them.
theorem Foldl_max_ge_seed (a : Int) (xs : List Int) :
    a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact Int.le_refl a
  | cons z zs ih =>
    have h1 : a ≤ max a z := Int.le_max_left a z
    exact Int.le_trans h1 (ih (max a z))

theorem Foldl_max_ge_mem (a x : Int) (xs : List Int) (h : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at h
  | cons z zs ih =>
    rcases List.mem_cons.mp h with h1 | h1
    · subst h1
      have h2 : x ≤ max a x := Int.le_max_right a x
      exact Int.le_trans h2 (Foldl_max_ge_seed (max a x) zs)
    · exact ih (max a z) h1

theorem Mem_le_ListMax (t : List Int) (x : Int) (h : x ∈ t) :
    x ≤ ListMax t := by
  cases t with
  | nil => simp at h
  | cons a rest =>
    rcases List.mem_cons.mp h with h1 | h1
    · subst h1; exact Foldl_max_ge_seed x rest
    · exact Foldl_max_ge_mem a x rest h1

theorem GetD_mem_take (l : List Int) (m j : Nat)
    (hjm : j < m) (hjl : j < l.length) :
    l.getD j 0 ∈ l.take m := by
  induction l generalizing m j with
  | nil => simp at hjl
  | cons a rest ih =>
    cases m with
    | zero => omega
    | succ m2 =>
      cases j with
      | zero => simp [List.take_succ_cons]
      | succ j2 =>
        simp only [List.getD_cons_succ, List.take_succ_cons]
        exact List.mem_cons_of_mem a
          (ih m2 j2 (by omega) (by simpa using hjl))

theorem GetD_le_ListMax_take (l : List Int) (j i : Int)
    (h0 : 0 ≤ j) (h1 : j ≤ i) (h2 : i < (l.length : Int)) :
    l.getD (j).toNat 0 ≤ ListMax (l.take ((i + 1)).toNat) :=
  Mem_le_ListMax _ _ (GetD_mem_take l ((i + 1)).toNat (j).toNat
    (by omega) (by omega))

end VeriPy
""".format(version=PRELUDE_VERSION)

# Line count the prelude prepends before the first encoded definition —
# the encoder's line_map starts after it.
PRELUDE_LINES = PRELUDE.count("\n")
