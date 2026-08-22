// Gap lemma for is_prime (HumanEval/31).
//
// The canonical solution trial-divides range(2, n - 1) while the spec
// quantifies range(2, n): the missing index is n - 1, and the program
// is right anyway because n % (n - 1) == 1 whenever n >= 3. The Lean
// pack states the same fact (he_humaneval_31.proofs.lean); the two
// sidecars keep the source one program under both provers.

lemma ModPredOne(n: int)
  requires n >= 3
  ensures PyMod(n, n - 1) == 1
{
  assert n == 1 * (n - 1) + 1;
}
