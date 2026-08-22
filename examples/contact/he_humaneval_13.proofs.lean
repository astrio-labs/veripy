-- Divisibility pack for greatest_common_divisor (HumanEval/13).
--
-- The invariant carries the loop's whole meaning in one quantified
-- conjunct: the common divisors of (x, y) are exactly the common
-- divisors of (a, b). Stepping it across `x, y = y, x % y` needs the
-- Euclid exchange -- d divides both y and x%y exactly when it divides
-- both x and y -- for every divisor d in the window at once.
--
-- EuclidStepAll is stated to MIRROR the invariant's own quantifier
-- shape (`∀ d, (1 ≤ d ∧ d < m) → ...iff...`), so the preservation
-- simp_all can use it as a conditional rewrite whose side conditions
-- are the binder's own bounds. It is hypothesis-free in x and y: the
-- iff holds for every y, including y = 0 (where fmod x 0 = x and both
-- sides coincide) and negative y, so nothing needs discharging at the
-- instantiation site.
--
-- FmodCongr is the load-bearing step: fmod x y ≡ x (mod d) whenever
-- d ∣ y. Proved via Int.fmod_eq_emod, whose `if` contributes either 0
-- or y -- and both vanish mod d.

theorem FmodCongr (x y d : Int) (hy : d ∣ y) :
    (Int.fmod x y) % d = x % d := by
  rw [Int.fmod_eq_emod]
  split
  · rw [Int.add_zero, Int.emod_emod_of_dvd x hy]
  · rw [Int.add_emod, Int.emod_emod_of_dvd x hy,
        Int.emod_eq_zero_of_dvd hy, Int.add_zero,
        Int.emod_emod_of_dvd _ (Int.dvd_refl d)]

theorem EuclidStepAll (x y m : Int) :
    ∀ d : Int, (1 ≤ d ∧ d < m) →
      ((VeriPy.PyMod y d = 0 ∧ VeriPy.PyMod (VeriPy.PyMod x y) d = 0) ↔
        (VeriPy.PyMod x d = 0 ∧ VeriPy.PyMod y d = 0)) := by
  intro d hd
  have hdpos : (0:Int) < d := by omega
  rw [VeriPy.PyMod_pos y d hdpos, VeriPy.PyMod_pos x d hdpos,
      VeriPy.PyMod_pos (VeriPy.PyMod x y) d hdpos]
  unfold VeriPy.PyMod
  constructor
  · rintro ⟨hy, hw⟩
    have h := FmodCongr x y d (Int.dvd_of_emod_eq_zero hy)
    exact ⟨by omega, hy⟩
  · rintro ⟨hx, hy⟩
    have h := FmodCongr x y d (Int.dvd_of_emod_eq_zero hy)
    exact ⟨hy, by omega⟩
