-- The keystone: a composite's smallest factor is at most its square
-- root, so a clean window [2, k) with k*k > n certifies the FULL
-- window [2, n).

theorem CompositeHasSmallFactor (n k : Int)
    (h2 : 2 ≤ n) (hk2 : 2 ≤ k) (hk : n < k * k)
    (hclean : ∀ j : Int, 2 ≤ j → j < k → ¬(VeriPy.PyMod n j = 0)) :
    ∀ d : Int, 2 ≤ d → d < n → ¬(VeriPy.PyMod n d = 0) := by
  intro d hd2 hdn hmod
  rw [VeriPy.PyMod_pos n d (by omega)] at hmod
  have hdvd : d ∣ n := Int.dvd_of_emod_eq_zero hmod
  obtain ⟨e, he⟩ := hdvd
  have he1 : 1 ≤ e := by
    rcases Classical.em (1 ≤ e) with h | h
    · exact h
    · have he0 : e ≤ 0 := by omega
      have hh : d * e ≤ d * 0 := Int.mul_le_mul_of_nonneg_left he0 (by omega)
      rw [Int.mul_zero] at hh
      omega
  have he2 : 2 ≤ e := by
    rcases Classical.em (e = 1) with h | h
    · subst h
      rw [Int.mul_one] at he
      omega
    · omega
  have hsplit : d < k ∨ e < k := by
    rcases Classical.em (d < k) with h | h
    · exact Or.inl h
    · right
      rcases Classical.em (e < k) with h3 | h3
      · exact h3
      · exfalso
        have hkk : k * k ≤ d * e :=
          Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
        omega
  rcases hsplit with h | h
  · exact hclean d hd2 h (by rw [VeriPy.PyMod_pos n d (by omega)]; exact hmod)
  · have hmode : n % e = 0 := by
      rw [he, Int.mul_comm]
      exact Int.mul_emod_right e d
    exact hclean e he2 h (by rw [VeriPy.PyMod_pos n e (by omega)]; exact hmode)
