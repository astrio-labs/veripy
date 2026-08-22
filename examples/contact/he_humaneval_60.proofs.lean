-- Proof pack for sum_to_n (HumanEval/60).
--
-- Stepping the invariant `total == (i-1)*i//2` to
-- `total + i == i*(i+1)//2` needs the product of two consecutive
-- integers to be even. Without that the two floor divisions are opaque
-- atoms and omega cannot relate them.
--
-- Stronger than the Dafny pack of the same name, deliberately. That one
-- carries `requires i >= 1` and leans on a recursive ConsecutiveEven
-- helper defined only for k >= 0. The Lean encoder instantiates a
-- `#@ proof` clause as `have hwp0 := GaussStep «i»`, with nowhere to
-- discharge a side condition, so a lemma with a hypothesis would land in
-- the context as a FUNCTION rather than a fact and help nothing. It is
-- true for every integer anyway: i*i - i is even whichever parity i has.

theorem GaussStep (i : Int) :
    VeriPy.PyFloorDiv ((i - 1) * i) 2 + i
      = VeriPy.PyFloorDiv (i * (i + 1)) 2 := by
  -- Python's `//` is fdiv; for a positive divisor it agrees with Lean's
  -- own `/`, which omega reasons about natively for a constant divisor.
  rw [VeriPy.PyFloorDiv_pos _ _ (by omega : (0:Int) < 2),
      VeriPy.PyFloorDiv_pos _ _ (by omega : (0:Int) < 2)]
  -- Core Lean has no `ring`, so both products are rewritten to the
  -- normal form `i * i ± i` by hand and omega treats `i * i` as an atom.
  have hexp1 : (i - 1) * i = i * i - i := by
    rw [Int.sub_mul, Int.one_mul]
  have hexp2 : i * (i + 1) = i * i + i := by
    rw [Int.mul_add, Int.mul_one]
  rw [hexp1, hexp2]
  -- The evenness that makes the two halvings line up. By parity of i:
  -- both i*i and i cancel mod 2 either way.
  have hev : (i * i - i) % 2 = 0 := by
    have h : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases h with h | h <;> simp [Int.sub_emod, Int.mul_emod, h]
  omega
