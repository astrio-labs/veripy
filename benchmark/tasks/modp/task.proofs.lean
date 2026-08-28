-- Proof pack for modp (HumanEval/49): 2^n mod p by repeated doubling.
--
-- The invariant `ret == (2 ** i) % p` steps to `(2 * ret) % p ==
-- (2 ** (i+1)) % p`, which needs two facts the fixed cocktail cannot
-- reach: dropping an inner reduction (ModMulLeft) and unrolling the
-- power one step (PowStepTwo).
--
-- ModMulLeft is stated with the multiplier on the LEFT and the reduced
-- factor on the RIGHT, matching the translated step `(2 * ret)`
-- verbatim -- the instantiation is `ModMulLeft (2 ** i) 2 p`, and a
-- commuted statement would leave simp a mul_comm bridge it does not
-- have. Hypothesis-free: it holds for every p, including p = 0, where
-- fmod is the identity and both sides are `b * a`.
--
-- PowStepTwo carries `0 ≤ i`, which the instantiation site cannot
-- discharge -- it lands in the context as an implication, and the
-- preservation simp_all resolves it against the invariant's own
-- `0 ≤ i` conjunct. A hypothesis-free statement is impossible here:
-- PyPow clamps a negative exponent to zero, so at i = -1 the claim
-- would read 1 = 2.

theorem ModMulLeft (a b p : Int) :
    VeriPy.PyMod (b * VeriPy.PyMod a p) p = VeriPy.PyMod (b * a) p := by
  unfold VeriPy.PyMod
  rw [Int.mul_fmod, Int.fmod_fmod, ← Int.mul_fmod]

theorem PowStepTwo (i : Int) (h : 0 ≤ i) :
    VeriPy.PyPow 2 (i + 1) = 2 * VeriPy.PyPow 2 i := by
  rw [VeriPy.PyPow_succ 2 i h]
  omega
