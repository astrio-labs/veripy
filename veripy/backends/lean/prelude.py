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

PRELUDE_VERSION = "lean-0.17"

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

-- The dict model for the frequency class (mbpp_97): an
-- association list over (Int × Int), all operations structural
-- so every lemma is a clean if-split induction. Order is carried
-- but never observed — the admitted specs are order-blind, per
-- the iteration-order veto. FreqFold_inv is the MASTER invariant
-- (lookup = prefix count, membership both ways, value-sum =
-- prefix index): strictly stronger than the source's three
-- invariant lines, which the class ABSORBS the way the
-- nested-search flattener absorbs inner-loop invariants — their
-- meaning is carried, and they stay live for the Dafny backend.
def DictGet : List (Int × Int) → Int → Int
  | [], _ => 0
  | (a, v) :: rest, k => if a = k then v else DictGet rest k

def DictHas : List (Int × Int) → Int → Bool
  | [], _ => false
  | (a, _) :: rest, k => if a = k then true else DictHas rest k

def DictSum : List (Int × Int) → Int
  | [] => 0
  | (_, v) :: rest => v + DictSum rest

def DictBump : List (Int × Int) → Int → List (Int × Int)
  | [], k => [(k, 1)]
  | (a, v) :: rest, k =>
      if a = k then (a, v + 1) :: rest
      else (a, v) :: DictBump rest k

theorem DictGet_bump_self (d : List (Int × Int)) (k : Int) :
    DictGet (DictBump d k) k = DictGet d k + 1 := by
  induction d with
  | nil => simp [DictBump, DictGet]
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    by_cases h : a = k
    · subst h
      simp [DictBump, DictGet]
    · simp [DictBump, DictGet, if_neg h, ih]

theorem DictGet_bump_other (d : List (Int × Int)) (k q : Int)
    (h : q ≠ k) : DictGet (DictBump d k) q = DictGet d q := by
  induction d with
  | nil =>
    simp [DictBump, DictGet]
    intro he
    exact absurd he.symm h
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    by_cases ha : a = k
    · subst ha
      have haq : ¬(a = q) := fun he => h he.symm
      simp [DictBump, DictGet, if_neg haq]
    · simp only [DictBump, if_neg ha]
      by_cases haq : a = q
      · simp [DictGet, if_pos haq]
      · simp [DictGet, if_neg haq, ih]

theorem DictHas_bump (d : List (Int × Int)) (k q : Int) :
    DictHas (DictBump d k) q = (DictHas d q || decide (q = k)) := by
  induction d with
  | nil =>
    by_cases h : k = q
    · subst h
      simp [DictBump, DictHas]
    · simp [DictBump, DictHas, if_neg h]
      intro he
      exact absurd he.symm h
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    by_cases ha : a = k
    · subst ha
      by_cases haq : a = q
      · subst haq
        simp [DictBump, DictHas]
      · simp [DictBump, DictHas, if_neg haq]
        intro he
        exact absurd he.symm haq
    · simp only [DictBump, if_neg ha]
      by_cases haq : a = q
      · simp [DictHas, if_pos haq]
      · simp [DictHas, if_neg haq, ih]

theorem DictSum_bump (d : List (Int × Int)) (k : Int) :
    DictSum (DictBump d k) = DictSum d + 1 := by
  induction d with
  | nil => simp [DictBump, DictSum]
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    by_cases h : a = k
    · subst h
      simp [DictBump, DictSum]
      omega
    · simp only [DictBump, if_neg h]
      simp only [DictSum]
      omega


-- Layer 2 of the frequency-class pin: the fuel fold over the
-- flattened list and the MASTER invariant (lookup = prefix count,
-- membership both ways, value-sum = prefix index, index in window).

def FreqFold (flat : List Int) : Nat → Int → List (Int × Int) → List (Int × Int)
  | 0, _, d => d
  | (m_ + 1), i_, d =>
      if i_ < (flat.length : Int) then
        FreqFold flat m_ (i_ + 1) (DictBump d (flat.getD (i_).toNat 0))
      else d

def FreqInv (flat : List Int) (i_ : Int) (d : List (Int × Int)) : Prop :=
  (∀ q : Int, DictGet d q = ((flat.take (i_).toNat).count q : Int))
  ∧ (∀ q : Int, DictHas d q = true ↔ q ∈ flat.take (i_).toNat)
  ∧ (DictSum d = i_)
  ∧ (0 ≤ i_ ∧ i_ ≤ (flat.length : Int))

theorem FreqFold_inv (flat : List Int) : ∀ (m_ : Nat) (i_ : Int) (d : List (Int × Int)),
    FreqInv flat i_ d → (flat.length : Int) ≤ i_ + (m_ : Int) →
    FreqInv flat ((flat.length : Int)) (FreqFold flat m_ i_ d) := by
  intro m_
  induction m_ with
  | zero =>
      intro i_ d h hb
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hie : i_ = (flat.length : Int) := by omega
      subst hie
      simpa only [FreqFold] using ⟨h1, h2, h3, h4⟩
  | succ m2 ih =>
      intro i_ d h hb
      obtain ⟨h1, h2, h3, h4⟩ := h
      by_cases hc : i_ < (flat.length : Int)
      · simp only [FreqFold, if_pos hc]
        apply ih
        · have hlt : (i_).toNat < flat.length := by omega
          have hx := Take_succ_getD flat (i_).toNat hlt
          have hstep : flat.take ((i_ + 1)).toNat
              = flat.take (i_).toNat ++ [flat.getD (i_).toNat 0] := by
            rw [show ((i_ + 1)).toNat = (i_).toNat + 1 from by omega]
            exact hx
          refine ⟨?_, ?_, ?_, by omega⟩
          · intro q
            rw [hstep]
            rw [List.count_append]
            by_cases hq : q = flat.getD (i_).toNat 0
            · rw [hq, DictGet_bump_self,
                  h1 (flat.getD (i_).toNat 0)]
              simp [List.count_cons]
              try push_cast
              try omega
            · rw [DictGet_bump_other d _ q hq, h1 q]
              have : ([flat.getD (i_).toNat 0].count q) = 0 := by
                simp [List.count_cons]
                intro he
                exact absurd he.symm hq
              rw [this]
              push_cast
              omega
          · intro q
            rw [hstep, DictHas_bump]
            constructor
            · intro hq
              rcases Bool.or_eq_true_iff.mp hq with hq1 | hq1
              · exact List.mem_append_left _ ((h2 q).mp hq1)
              · have := of_decide_eq_true hq1
                subst this
                exact List.mem_append_right _ (by simp)
            · intro hq
              rcases List.mem_append.mp hq with hq1 | hq1
              · exact Bool.or_eq_true_iff.mpr
                  (Or.inl ((h2 q).mpr hq1))
              · have : q = flat.getD (i_).toNat 0 := by simpa using hq1
                exact Bool.or_eq_true_iff.mpr
                  (Or.inr (decide_eq_true this))
          · rw [DictSum_bump]
            omega
        · push_cast
          omega
      · have hie : i_ = (flat.length : Int) := by omega
        subst hie
        simp only [FreqFold, if_neg hc]
        exact ⟨h1, h2, h3, h4⟩


theorem PySum_map_length_flatten (l : List (List Int)) :
    PySum (l.map (fun s => ((s.length : Int))))
      = ((l.flatten.length : Int)) := by
  induction l with
  | nil => simp [PySum]
  | cons s rest ih =>
    simp only [List.map_cons, PySum, List.flatten_cons,
               List.length_append, ih]
    push_cast
    omega

-- The isomorphism-class pack (mbpp_885): position-class dicts
-- over code-point strings. AppendPos inserts fresh keys at the
-- END, so the value order is FIRST-OCCURRENCE order — a property
-- of the position partition alone, which is why the ⇐ direction
-- gets literally equal value lists (IsoVals) and the sort needs
-- no properties beyond being a permutation (SortL_perm): both
-- sides of the algorithm's test reduce to multiset equality of
-- the partition blocks, which the spec theorem proves equivalent
-- to the ∀∀ equality pattern. The masters (PosFold_inv, the
-- pointwise/fresh Vals lemmas) absorb the source's four
-- invariant lines, the nested-search flattener's precedent.
-- Stage A of the isomorphism-class pin (mbpp_885): the position-
-- class dict. Keys are code points, values are the (increasing)
-- lists of positions where the key occurs. AppendPos inserts at the
-- END on a fresh key, so the value order is first-occurrence order —
-- which is determined by the position PARTITION alone, not by the
-- characters (the keystone of the ⇐ direction).

def DictGetL : List (Int × List Int) → Int → List Int
  | [], _ => []
  | (a, l) :: rest, c => if a = c then l else DictGetL rest c

def DictHasL : List (Int × List Int) → Int → Bool
  | [], _ => false
  | (a, _) :: rest, c => if a = c then true else DictHasL rest c

def AppendPos : List (Int × List Int) → Int → Int → List (Int × List Int)
  | [], c, i => [(c, [i])]
  | (a, l) :: rest, c, i =>
      if a = c then (a, l ++ [i]) :: rest
      else (a, l) :: AppendPos rest c i

def Vals (d : List (Int × List Int)) : List (List Int) :=
  d.map (fun p => p.2)

theorem GetL_appendPos_self (d : List (Int × List Int)) (c i : Int) :
    DictGetL (AppendPos d c i) c = DictGetL d c ++ [i] := by
  induction d with
  | nil => simp [AppendPos, DictGetL]
  | cons p rest ih =>
    obtain ⟨a, l⟩ := p
    by_cases h : a = c
    · subst h
      simp [AppendPos, DictGetL]
    · simp [AppendPos, DictGetL, if_neg h, ih]

theorem GetL_appendPos_other (d : List (Int × List Int)) (c q i : Int)
    (h : q ≠ c) : DictGetL (AppendPos d c i) q = DictGetL d q := by
  induction d with
  | nil =>
    simp [AppendPos, DictGetL]
    intro he
    exact absurd he.symm h
  | cons p rest ih =>
    obtain ⟨a, l⟩ := p
    by_cases ha : a = c
    · subst ha
      have haq : ¬(a = q) := fun he => h he.symm
      simp [AppendPos, DictGetL, if_neg haq]
    · simp only [AppendPos, if_neg ha]
      by_cases haq : a = q
      · simp [DictGetL, if_pos haq]
      · simp [DictGetL, if_neg haq, ih]

theorem HasL_appendPos (d : List (Int × List Int)) (c q i : Int) :
    DictHasL (AppendPos d c i) q = (DictHasL d q || decide (q = c)) := by
  induction d with
  | nil =>
    by_cases h : c = q
    · subst h
      simp [AppendPos, DictHasL]
    · simp [AppendPos, DictHasL, if_neg h]
      intro he
      exact absurd he.symm h
  | cons p rest ih =>
    obtain ⟨a, l⟩ := p
    by_cases ha : a = c
    · subst ha
      by_cases haq : a = q
      · subst haq
        simp [AppendPos, DictHasL]
      · simp [AppendPos, DictHasL, if_neg haq]
        intro he
        exact absurd he.symm haq
    · simp only [AppendPos, if_neg ha]
      by_cases haq : a = q
      · simp [DictHasL, if_pos haq]
      · simp [DictHasL, if_neg haq, ih]

-- Fresh keys append their block at the END; known keys touch only
-- their own slot. The Vals facts the ⇐ joint induction rides.
theorem Vals_appendPos_fresh (d : List (Int × List Int)) (c i : Int)
    (h : DictHasL d c = false) :
    Vals (AppendPos d c i) = Vals d ++ [[i]] := by
  induction d with
  | nil => simp [AppendPos, Vals]
  | cons p rest ih =>
    obtain ⟨a, l⟩ := p
    by_cases ha : a = c
    · subst ha
      simp [DictHasL] at h
    · simp only [DictHasL, if_neg ha] at h
      have hi := ih h
      simp only [Vals, List.map_cons] at hi ⊢
      simp [AppendPos, if_neg ha, hi]

def KeysNodup : List (Int × List Int) → Prop
  | [] => True
  | (a, _) :: rest => DictHasL rest a = false ∧ KeysNodup rest

theorem HasL_false_of_appendPos (d : List (Int × List Int))
    (a c i : Int) (hne : a ≠ c) (h : DictHasL d a = false) :
    DictHasL (AppendPos d c i) a = false := by
  rw [HasL_appendPos]
  simp [h]
  intro he
  exact absurd he hne

theorem KeysNodup_appendPos (d : List (Int × List Int)) (c i : Int)
    (h : KeysNodup d) : KeysNodup (AppendPos d c i) := by
  induction d with
  | nil => simp [AppendPos, KeysNodup, DictHasL]
  | cons p rest ih =>
    obtain ⟨a, l⟩ := p
    obtain ⟨h1, h2⟩ := h
    by_cases ha : a = c
    · subst ha
      simp only [AppendPos, if_pos rfl]
      exact ⟨h1, h2⟩
    · simp only [AppendPos, if_neg ha]
      exact ⟨HasL_false_of_appendPos rest a c i ha h1, ih h2⟩

-- Known keys: AppendPos rewrites exactly one slot, and Vals changes
-- pointwise at that slot. Stated as the Forall₂ the joint induction
-- carries: two dicts with pointwise-equal values stay pointwise
-- equal when each appends to the slot of a SHARED block.
theorem Vals_appendPos_known_pointwise
    (d1 d2 : List (Int × List Int)) (c1 c2 i : Int)
    (hlen : Vals d1 = Vals d2)
    (hsame : DictGetL d1 c1 = DictGetL d2 c2)
    (hh1 : DictHasL d1 c1 = true) (hh2 : DictHasL d2 c2 = true)
    (hn1 : KeysNodup d1) (hn2 : KeysNodup d2)
    (hkey1 : ∀ k q, DictHasL d1 k = true → DictHasL d1 q = true →
       k ≠ q → DictGetL d1 k ≠ DictGetL d1 q)
    (hkey2 : ∀ k q, DictHasL d2 k = true → DictHasL d2 q = true →
       k ≠ q → DictGetL d2 k ≠ DictGetL d2 q) :
    Vals (AppendPos d1 c1 i) = Vals (AppendPos d2 c2 i) := by
  induction d1 generalizing d2 with
  | nil => simp [DictHasL] at hh1
  | cons p rest ih =>
    obtain ⟨a, l⟩ := p
    cases d2 with
    | nil => simp [DictHasL] at hh2
    | cons pq rest2 =>
      obtain ⟨b, m⟩ := pq
      have hval : l = m := by
        simpa [Vals] using congrArg (fun x => x.headD []) hlen
      have hrest : Vals rest = Vals rest2 := by
        simpa [Vals] using congrArg List.tail hlen
      by_cases ha : a = c1
      · subst ha
        have hb : b = c2 := by
          by_cases hb2 : b = c2
          · exact hb2
          · exfalso
            have hs1 : DictGetL ((a, l) :: rest) a = l := by
              simp [DictGetL]
            have hs2 : DictGetL ((b, m) :: rest2) c2
                = DictGetL rest2 c2 := by
              simp [DictGetL, if_neg hb2]
            have hgb : DictGetL ((b, m) :: rest2) b = m := by
              simp [DictGetL]
            have hd : DictGetL ((b, m) :: rest2) b
                = DictGetL ((b, m) :: rest2) c2 := by
              rw [hgb, hs2, ← hval]
              rw [hs1] at hsame
              rw [hs2] at hsame
              exact hsame
            exact hkey2 b c2 (by simp [DictHasL]) hh2
              (fun he => hb2 he) hd
        subst hb
        simp only [AppendPos, if_true]
        simp only [Vals, List.map_cons]
        have hrest' := hrest
        simp only [Vals] at hrest'
        rw [hval, hrest']
      · have hb : b ≠ c2 := by
          intro hb2
          subst hb2
          have hs1 : DictGetL ((a, l) :: rest) c1
              = DictGetL rest c1 := by
            simp [DictGetL, if_neg ha]
          have hga : DictGetL ((a, l) :: rest) a = l := by
            simp [DictGetL]
          have hgb : DictGetL ((b, m) :: rest2) b = m := by
            simp [DictGetL]
          have hd : DictGetL ((a, l) :: rest) a
              = DictGetL ((a, l) :: rest) c1 := by
            rw [hga, hs1]
            rw [hs1] at hsame
            rw [hgb] at hsame
            rw [hsame, hval]
          exact hkey1 a c1 (by simp [DictHasL]) hh1 ha hd
        simp only [AppendPos, if_neg ha, if_neg hb]
        simp only [Vals, List.map_cons]
        have htail : Vals (AppendPos rest c1 i)
            = Vals (AppendPos rest2 c2 i) := by
          have hh1r : DictHasL rest c1 = true := by
            simpa [DictHasL, if_neg ha] using hh1
          have hh2r : DictHasL rest2 c2 = true := by
            simpa [DictHasL, if_neg hb] using hh2
          have hsr : DictGetL rest c1 = DictGetL rest2 c2 := by
            have e1 : DictGetL ((a, l) :: rest) c1
                = DictGetL rest c1 := by simp [DictGetL, if_neg ha]
            have e2 : DictGetL ((b, m) :: rest2) c2
                = DictGetL rest2 c2 := by simp [DictGetL, if_neg hb]
            rw [e1, e2] at hsame
            exact hsame
          have hk1r : ∀ k q, DictHasL rest k = true →
              DictHasL rest q = true → k ≠ q →
              DictGetL rest k ≠ DictGetL rest q := by
            intro k q hk hq hne
            have hka : k ≠ a := by
              intro he; subst he
              rw [hn1.1] at hk; exact absurd hk (by simp)
            have hqa : q ≠ a := by
              intro he; subst he
              rw [hn1.1] at hq; exact absurd hq (by simp)
            have hak : ¬(a = k) := fun he => hka he.symm
            have haq2 : ¬(a = q) := fun he => hqa he.symm
            have := hkey1 k q
              (by simp [DictHasL, if_neg hak, hk])
              (by simp [DictHasL, if_neg haq2, hq])
              hne
            simpa [DictGetL, if_neg hak, if_neg haq2] using this
          have hk2r : ∀ k q, DictHasL rest2 k = true →
              DictHasL rest2 q = true → k ≠ q →
              DictGetL rest2 k ≠ DictGetL rest2 q := by
            intro k q hk hq hne
            have hkb : k ≠ b := by
              intro he; subst he
              rw [hn2.1] at hk; exact absurd hk (by simp)
            have hqb : q ≠ b := by
              intro he; subst he
              rw [hn2.1] at hq; exact absurd hq (by simp)
            have hbk : ¬(b = k) := fun he => hkb he.symm
            have hbq : ¬(b = q) := fun he => hqb he.symm
            have := hkey2 k q
              (by simp [DictHasL, if_neg hbk, hk])
              (by simp [DictHasL, if_neg hbq, hq])
              hne
            simpa [DictGetL, if_neg hbk, if_neg hbq] using this
          exact ih rest2 hrest hsr hh1r hh2r hn1.2 hn2.2 hk1r hk2r
        have htail' := htail
        simp only [Vals] at htail'
        rw [hval, htail']



-- Stage A2: the per-string fold and its EXACT-LIST master invariant.
-- DictGetL of the fold at c is literally the filtered index range —
-- stronger than a membership characterization, and exactly what lets
-- the ⇐ direction close by filter_congr under the pattern.

def IntRange (i : Int) : List Int :=
  (List.range (i).toNat).map (fun n => ((n : Nat) : Int))

def PosList (s : List Int) (i c : Int) : List Int :=
  (IntRange i).filter (fun j => decide (s.getD (j).toNat 0 = c))

def PosFold (s : List Int) : Nat → Int → List (Int × List Int) → List (Int × List Int)
  | 0, _, d => d
  | (m_ + 1), i_, d =>
      if i_ < (s.length : Int) then
        PosFold s m_ (i_ + 1) (AppendPos d (s.getD (i_).toNat 0) i_)
      else d

def PosInv (s : List Int) (i_ : Int) (d : List (Int × List Int)) : Prop :=
  (∀ c : Int, DictGetL d c = PosList s i_ c)
  ∧ (∀ c : Int, DictHasL d c = true ↔ DictGetL d c ≠ [])
  ∧ KeysNodup d
  ∧ (0 ≤ i_ ∧ i_ ≤ (s.length : Int))

theorem IntRange_succ (i : Int) (h : 0 ≤ i) :
    IntRange (i + 1) = IntRange i ++ [i] := by
  unfold IntRange
  rw [show ((i + 1)).toNat = (i).toNat + 1 from by omega]
  rw [List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 2
  omega

theorem PosList_succ (s : List Int) (i c : Int) (h : 0 ≤ i) :
    PosList s (i + 1) c
      = PosList s i c
        ++ (if s.getD (i).toNat 0 = c then [i] else []) := by
  unfold PosList
  rw [IntRange_succ i h, List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  by_cases hc : s.getD (i).toNat 0 = c
  · rw [decide_eq_true hc, if_pos hc]
    rfl
  · rw [decide_eq_false hc, if_neg hc]
    rfl

-- has ↔ nonempty survives an AppendPos.
theorem HasL_iff_ne_nil_appendPos (d : List (Int × List Int))
    (c i : Int)
    (h : ∀ q : Int, DictHasL d q = true ↔ DictGetL d q ≠ []) :
    ∀ q : Int, DictHasL (AppendPos d c i) q = true
      ↔ DictGetL (AppendPos d c i) q ≠ [] := by
  intro q
  by_cases hq : q = c
  · subst hq
    rw [GetL_appendPos_self]
    rw [HasL_appendPos]
    simp
  · rw [GetL_appendPos_other d c q i hq,
        HasL_appendPos]
    constructor
    · intro hh
      rcases Bool.or_eq_true_iff.mp hh with h1 | h1
      · exact (h q).mp h1
      · exact absurd (of_decide_eq_true h1) hq
    · intro hne
      exact Bool.or_eq_true_iff.mpr (Or.inl ((h q).mpr hne))

-- The single step, extracted: both PosFold_inv and the ⇐ joint
-- induction ride it.
theorem PosInv_step (s : List Int) (i_ : Int)
    (d : List (Int × List Int)) (h : PosInv s i_ d)
    (hc : i_ < (s.length : Int)) :
    PosInv s (i_ + 1) (AppendPos d (s.getD (i_).toNat 0) i_) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, HasL_iff_ne_nil_appendPos d _ i_ h2,
          KeysNodup_appendPos d _ i_ h3, by omega⟩
  intro c
  rw [PosList_succ s i_ c (by omega)]
  by_cases hq : c = s.getD (i_).toNat 0
  · rw [hq, GetL_appendPos_self, h1 (s.getD (i_).toNat 0)]
    simp
  · rw [GetL_appendPos_other d _ c i_ hq, h1 c]
    have hnc : ¬(s.getD (i_).toNat 0 = c) :=
      fun he => hq he.symm
    rw [if_neg hnc, List.append_nil]

theorem PosFold_inv (s : List Int) : ∀ (m_ : Nat) (i_ : Int) (d : List (Int × List Int)),
    PosInv s i_ d → (s.length : Int) ≤ i_ + (m_ : Int) →
    PosInv s ((s.length : Int)) (PosFold s m_ i_ d) := by
  intro m_
  induction m_ with
  | zero =>
      intro i_ d h hb
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hie : i_ = (s.length : Int) := by omega
      subst hie
      simpa only [PosFold] using ⟨h1, h2, h3, h4⟩
  | succ m2 ih =>
      intro i_ d h hb
      by_cases hc : i_ < (s.length : Int)
      · simp only [PosFold, if_pos hc]
        apply ih
        · exact PosInv_step s i_ d h hc
        · push_cast
          omega
      · obtain ⟨h1, h2, h3, h4⟩ := h
        have hie : i_ = (s.length : Int) := by omega
        subst hie
        simp only [PosFold, if_neg hc]
        exact ⟨h1, h2, h3, h4⟩



-- Stage B: the ⇐ joint induction. Under the equality pattern (and
-- equal lengths) the two folds build LITERALLY equal value lists —
-- first-occurrence order is a property of the position partition,
-- not of the characters.

theorem mem_IntRange (i j : Int) (h : 0 ≤ i) :
    j ∈ IntRange i ↔ (0 ≤ j ∧ j < i) := by
  unfold IntRange
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro ⟨h0, h1⟩
    exact ⟨(j).toNat, by omega, by omega⟩

theorem mem_PosList (s : List Int) (i c j : Int)
    (hm : j ∈ PosList s i c) : s.getD (j).toNat 0 = c := by
  unfold PosList at hm
  exact of_decide_eq_true (List.mem_filter.mp hm).2

theorem PosInv_key_distinct (s : List Int) (i_ : Int)
    (d : List (Int × List Int)) (h : PosInv s i_ d) :
    ∀ k q, DictHasL d k = true → DictHasL d q = true → k ≠ q →
      DictGetL d k ≠ DictGetL d q := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  intro k q hk hq hne he
  have hkne : DictGetL d k ≠ [] := (h2 k).mp hk
  rcases List.exists_mem_of_ne_nil _ hkne with ⟨j, hj⟩
  have hsk : s.getD (j).toNat 0 = k := by
    rw [h1 k] at hj
    exact mem_PosList s i_ k j hj
  have hsq : s.getD (j).toNat 0 = q := by
    rw [he, h1 q] at hj
    exact mem_PosList s i_ q j hj
  exact hne (hsk ▸ hsq)

theorem IsoVals (s1 s2 : List Int)
    (hlen : s1.length = s2.length)
    (hpat : ∀ i j : Int, 0 ≤ i → i < (s1.length : Int) →
       0 ≤ j → j < (s1.length : Int) →
       ((s1.getD (i).toNat 0 = s1.getD (j).toNat 0)
         ↔ (s2.getD (i).toNat 0 = s2.getD (j).toNat 0))) :
    ∀ (m_ : Nat) (i_ : Int) (d1 d2 : List (Int × List Int)),
    PosInv s1 i_ d1 → PosInv s2 i_ d2 → Vals d1 = Vals d2 →
    (s1.length : Int) ≤ i_ + (m_ : Int) →
    Vals (PosFold s1 m_ i_ d1) = Vals (PosFold s2 m_ i_ d2) := by
  intro m_
  induction m_ with
  | zero =>
      intro i_ d1 d2 hI1 hI2 hV hb
      simpa only [PosFold] using hV
  | succ m2 ih =>
      intro i_ d1 d2 hI1 hI2 hV hb
      by_cases hc : i_ < (s1.length : Int)
      · have hc2 : i_ < (s2.length : Int) := by
          rw [← hlen]
          exact hc
        simp only [PosFold, if_pos hc, if_pos hc2]
        have h0 : 0 ≤ i_ := hI1.2.2.2.1
        -- the shared block: the two position classes of index i_
        have hsame : DictGetL d1 (s1.getD (i_).toNat 0)
            = DictGetL d2 (s2.getD (i_).toNat 0) := by
          rw [hI1.1 _, hI2.1 _]
          unfold PosList
          apply List.filter_congr
          intro j hj
          have hjb := (mem_IntRange i_ j h0).mp hj
          have hp := hpat j i_ hjb.1 (by omega) h0 hc
          by_cases h1j : s1.getD (j).toNat 0 = s1.getD (i_).toNat 0
          · rw [decide_eq_true h1j,
                decide_eq_true (hp.mp h1j)]
          · rw [decide_eq_false h1j,
                decide_eq_false (fun hx => h1j (hp.mpr hx))]
        have hst1 := PosInv_step s1 i_ d1 hI1 hc
        have hst2 := PosInv_step s2 i_ d2 hI2 hc2
        by_cases hf : DictHasL d1 (s1.getD (i_).toNat 0) = true
        · -- KNOWN on both sides (via hsame + has ↔ nonempty)
          have hf2 : DictHasL d2 (s2.getD (i_).toNat 0) = true := by
            rw [hI2.2.1 _, ← hsame]
            exact (hI1.2.1 _).mp hf
          have hstep := Vals_appendPos_known_pointwise d1 d2
            (s1.getD (i_).toNat 0) (s2.getD (i_).toNat 0) i_
            hV hsame hf hf2 hI1.2.2.1 hI2.2.2.1
            (PosInv_key_distinct s1 i_ d1 hI1)
            (PosInv_key_distinct s2 i_ d2 hI2)
          exact ih (i_ + 1) _ _ hst1 hst2 hstep
            (by push_cast; omega)
        · -- FRESH on both sides
          have hff : DictHasL d1 (s1.getD (i_).toNat 0) = false :=
            Bool.eq_false_iff.mpr hf
          have hf2 : DictHasL d2 (s2.getD (i_).toNat 0) = false := by
            rw [Bool.eq_false_iff]
            intro h2t
            have := (hI2.2.1 _).mp h2t
            rw [← hsame] at this
            exact hf ((hI1.2.1 _).mpr this)
          have hV1 := Vals_appendPos_fresh d1
            (s1.getD (i_).toNat 0) i_ hff
          have hV2 := Vals_appendPos_fresh d2
            (s2.getD (i_).toNat 0) i_ hf2
          exact ih (i_ + 1) _ _ hst1 hst2
            (by rw [hV1, hV2, hV]) (by push_cast; omega)
      · have hc2 : ¬(i_ < (s2.length : Int)) := by
          rw [← hlen]
          exact hc
        simp only [PosFold, if_neg hc, if_neg hc2]
        exact hV



-- Stage C: sorting as an OPAQUE permutation. The theorem needs
-- nothing about the order: ⇐ gets literal equality of the inputs,
-- and ⇒ needs only that sorting permutes. (Whether this models
-- Python's sorted faithfully is settled by the spec theorem itself:
-- both conditions are equivalent to multiset equality, which is
-- what Python's canonical sort compares.)

def ListLEb : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true
      else if y < x then false
      else ListLEb xs ys

def InsertLL (x : List Int) : List (List Int) → List (List Int)
  | [] => [x]
  | y :: ys => if ListLEb x y then x :: y :: ys
               else y :: InsertLL x ys

def SortL : List (List Int) → List (List Int)
  | [] => []
  | x :: xs => InsertLL x (SortL xs)

theorem InsertLL_perm (x : List Int) (l : List (List Int)) :
    List.Perm (InsertLL x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    by_cases h : ListLEb x y = true
    · simp only [InsertLL, if_pos h]
      exact List.Perm.refl _
    · simp only [InsertLL, if_neg h]
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem SortL_perm (l : List (List Int)) :
    List.Perm (SortL l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    exact (InsertLL_perm x (SortL xs)).trans
      (List.Perm.cons x ih)

-- Stage D helpers: PosList membership both ways, and Vals ↔ GetL.
theorem mem_PosList_intro (s : List Int) (i c j : Int)
    (h0 : 0 ≤ j) (h1 : j < i) (hs : s.getD (j).toNat 0 = c) :
    j ∈ PosList s i c := by
  unfold PosList
  rw [List.mem_filter]
  exact ⟨(mem_IntRange i j (by omega)).mpr ⟨h0, h1⟩,
         decide_eq_true hs⟩

theorem mem_PosList_bounds (s : List Int) (i c j : Int)
    (h : 0 ≤ i) (hm : j ∈ PosList s i c) : 0 ≤ j ∧ j < i := by
  unfold PosList at hm
  exact (mem_IntRange i j h).mp (List.mem_filter.mp hm).1

theorem Vals_mem_getL (d : List (Int × List Int))
    (hn : KeysNodup d) (l : List Int) (hm : l ∈ Vals d) :
    ∃ c : Int, DictHasL d c = true ∧ DictGetL d c = l := by
  induction d with
  | nil => simp [Vals] at hm
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    simp only [Vals, List.map_cons, List.mem_cons] at hm
    rcases hm with hm | hm
    · exact ⟨a, by simp [DictHasL], by simp [DictGetL, hm.symm]⟩
    · obtain ⟨c, hc1, hc2⟩ := ih hn.2 hm
      have hca : c ≠ a := by
        intro he
        subst he
        rw [hn.1] at hc1
        exact absurd hc1 (by simp)
      have hac : ¬(a = c) := fun he => hca he.symm
      exact ⟨c, by simp [DictHasL, if_neg hac, hc1],
             by simp [DictGetL, if_neg hac, hc2]⟩

theorem getL_mem_Vals (d : List (Int × List Int)) (c : Int)
    (h : DictHasL d c = true) : DictGetL d c ∈ Vals d := by
  induction d with
  | nil => simp [DictHasL] at h
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    by_cases ha : a = c
    · simp [DictGetL, if_pos ha, Vals]
    · simp only [DictHasL, if_neg ha] at h
      simp only [DictGetL, if_neg ha, Vals, List.map_cons]
      exact List.mem_cons_of_mem _ (ih h)



-- Stage D: the assembly. One direction is literal Vals equality
-- (IsoVals); the other rides the permutation through the block
-- structure of the exit invariants.

theorem PosList_zero (s : List Int) (c : Int) :
    PosList s 0 c = [] := rfl

theorem PosInv_entry (s : List Int) : PosInv s 0 [] := by
  refine ⟨fun c => (PosList_zero s c).symm, fun c => by
    simp [DictHasL, DictGetL], trivial, by
    constructor
    · omega
    · push_cast
      omega⟩

theorem pattern_of_valsPerm (s1 s2 : List Int)
    (F1 F2 : List (Int × List Int))
    (hI1 : PosInv s1 ((s1.length : Int)) F1)
    (hI2 : PosInv s2 ((s2.length : Int)) F2)
    (hperm : List.Perm (Vals F1) (Vals F2)) :
    ∀ i j : Int, 0 ≤ i → i < (s1.length : Int) →
      0 ≤ j → j < (s1.length : Int) →
      s1.getD (i).toNat 0 = s1.getD (j).toNat 0 →
      s2.getD (i).toNat 0 = s2.getD (j).toNat 0 := by
  intro i j hi0 hi1 hj0 hj1 hij
  have hBg : DictGetL F1 (s1.getD (i).toNat 0)
      = PosList s1 ((s1.length : Int)) (s1.getD (i).toNat 0) :=
    hI1.1 _
  have hiB : i ∈ DictGetL F1 (s1.getD (i).toNat 0) := by
    rw [hBg]
    exact mem_PosList_intro s1 _ _ i hi0 hi1 rfl
  have hjB : j ∈ DictGetL F1 (s1.getD (i).toNat 0) := by
    rw [hBg]
    exact mem_PosList_intro s1 _ _ j hj0 hj1 hij.symm
  have hhas : DictHasL F1 (s1.getD (i).toNat 0) = true :=
    (hI1.2.1 _).mpr (by
      intro he
      rw [he] at hiB
      simp at hiB)
  have hBV : DictGetL F1 (s1.getD (i).toNat 0) ∈ Vals F2 :=
    (hperm.mem_iff).mp (getL_mem_Vals F1 _ hhas)
  obtain ⟨c2, hc2has, hc2get⟩ :=
    Vals_mem_getL F2 hI2.2.2.1 _ hBV
  have hB2 : DictGetL F1 (s1.getD (i).toNat 0)
      = PosList s2 ((s2.length : Int)) c2 := by
    rw [← hc2get]
    exact (hI2.1 c2).symm ▸ rfl
  have hsi : s2.getD (i).toNat 0 = c2 :=
    mem_PosList s2 _ _ i (hB2 ▸ hiB)
  have hsj : s2.getD (j).toNat 0 = c2 :=
    mem_PosList s2 _ _ j (hB2 ▸ hjB)
  rw [hsi, hsj]

theorem bound_of_valsPerm (s1 s2 : List Int)
    (F1 F2 : List (Int × List Int))
    (hI1 : PosInv s1 ((s1.length : Int)) F1)
    (hI2 : PosInv s2 ((s2.length : Int)) F2)
    (hperm : List.Perm (Vals F1) (Vals F2)) :
    ∀ i : Int, 0 ≤ i → i < (s1.length : Int) →
      i < (s2.length : Int) := by
  intro i hi0 hi1
  have hBg := hI1.1 (s1.getD (i).toNat 0)
  have hiB : i ∈ DictGetL F1 (s1.getD (i).toNat 0) := by
    rw [hBg]
    exact mem_PosList_intro s1 _ _ i hi0 hi1 rfl
  have hhas : DictHasL F1 (s1.getD (i).toNat 0) = true :=
    (hI1.2.1 _).mpr (by
      intro he
      rw [he] at hiB
      simp at hiB)
  have hBV : DictGetL F1 (s1.getD (i).toNat 0) ∈ Vals F2 :=
    (hperm.mem_iff).mp (getL_mem_Vals F1 _ hhas)
  obtain ⟨c2, hc2has, hc2get⟩ :=
    Vals_mem_getL F2 hI2.2.2.1 _ hBV
  have hB2 : DictGetL F1 (s1.getD (i).toNat 0)
      = PosList s2 ((s2.length : Int)) c2 := by
    rw [← hc2get]
    exact (hI2.1 c2).symm ▸ rfl
  exact (mem_PosList_bounds s2 _ c2 i (by push_cast; omega)
    (hB2 ▸ hiB)).2


end VeriPy
""".format(version=PRELUDE_VERSION)

# Line count the prelude prepends before the first encoded definition —
# the encoder's line_map starts after it.
PRELUDE_LINES = PRELUDE.count("\n")
