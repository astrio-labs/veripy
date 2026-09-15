-- Shared checked proof support; expanded into each standalone artifact.

theorem FloorDivFacts (a b : Int) :
    a=Int.fdiv a b*b+Int.fmod a b ∧
    (b>0 → 0≤Int.fmod a b ∧ Int.fmod a b<b) ∧
    (b<0 → b<Int.fmod a b ∧ Int.fmod a b≤0) ∧
    Int.fmod (Int.fdiv a b*b) b=0 := by
  refine ⟨(Int.fdiv_mul_add_fmod a b).symm,?_,?_,Int.mul_fmod_left _ _⟩
  · intro h;exact ⟨Int.fmod_nonneg_of_pos a h,Int.fmod_lt_of_pos a h⟩
  · intro h
    rw [Int.fmod_eq_emod]
    have rem:=Int.emod_nonneg a (by omega : b≠0)
    have bound:=Int.emod_lt a (by omega : b≠0)
    have ab : (b.natAbs:Int) = -b := by omega
    rw [ab] at bound
    by_cases divides : b ∣ a
    · rw [if_pos (Or.inr divides),Int.emod_eq_zero_of_dvd divides]
      omega
    · rw [if_neg (by omega : ¬(0≤b ∨ b ∣ a))]
      have nonzero : a%b≠0 := fun hz=>divides (Int.dvd_of_emod_eq_zero hz)
      omega
