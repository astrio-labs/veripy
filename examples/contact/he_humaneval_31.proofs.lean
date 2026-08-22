-- Gap lemma for is_prime (HumanEval/31).
--
-- The canonical solution trial-divides over range(2, n - 1) while the
-- spec quantifies range(2, n): the missing index is n - 1, and the
-- program is right anyway because n % (n - 1) = 1 whenever n >= 3.
-- That single fact is what extends the loop's forall to the spec's.
--
-- The hypothesis 3 <= n is necessary: at n = 2 the claim would read
-- 2 % 1 = 1, and 2 % 1 = 0. The endgame discharges it by omega at
-- the instantiation site, where k = n - 1 and 2 <= k are in context.

theorem ModPredOne (n : Int) (h : 3 ≤ n) :
    VeriPy.PyMod n (n - 1) = 1 := by
  rw [VeriPy.PyMod_pos n (n - 1) (by omega)]
  have hpred : (1 : Int) % (n - 1) = 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  calc n % (n - 1) = (1 + (n - 1) * 1) % (n - 1) := by
        congr 1
        omega
    _ = 1 % (n - 1) := by rw [Int.add_mul_emod_self_left]
    _ = 1 := hpred
