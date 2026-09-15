-- Shared checked proof support; expanded into each standalone artifact.

theorem AllocationFacts (cur committed reserve p : Int) (hp : p > 0) :
    max cur ((committed + reserve + p - 1).fdiv p * p) ≥ cur ∧
    max cur ((committed + reserve + p - 1).fdiv p * p) ≥ committed + reserve ∧
    (max cur ((committed + reserve + p - 1).fdiv p * p) = cur ∨
      (max cur ((committed + reserve + p - 1).fdiv p * p)).fmod p = 0) := by
  have hd := Int.ediv_mul_add_emod (committed + reserve + p - 1) p
  have hb := Int.emod_lt_of_pos (committed + reserve + p - 1) hp
  have hf := Int.fdiv_eq_ediv_of_nonneg (committed + reserve + p - 1) (show 0 ≤ p by omega)
  rw [hf]
  constructor
  · omega
  constructor
  · omega
  by_cases h : cur ≥ (committed + reserve + p - 1) / p * p
  · left; omega
  · right
    have he : max cur ((committed + reserve + p - 1) / p * p) = (committed + reserve + p - 1) / p * p := by omega
    rw [he, Int.fmod_eq_emod]
    simp [show 0 ≤ p by omega]

theorem ReadWrite [Inhabited α] (xs : List α) (i j : Nat) (v : α) :
    (xs.set i v).getD j default = if i = j ∧ i < xs.length then v else xs.getD j default := by
  by_cases h : i = j
  · subst j
    by_cases hb : i < xs.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hb, hb]
    · simp [List.set_eq_of_length_le (show xs.length ≤ i by omega), hb]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, h]

theorem ReadCursor [Inhabited α] (pre suf : List α) (v : α) :
    (pre ++ v :: suf).getD pre.length default = v := by
  simp [List.getD_eq_getElem?_getD]
