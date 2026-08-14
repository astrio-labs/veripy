// Proof pack for sum_to_n (HumanEval/60).
//
// Stepping `total == (i-1)*i/2` to `total + i == i*(i+1)/2` needs the
// product of two consecutive integers to be even — otherwise the two
// floor divisions are opaque to the solver and the invariant is not
// maintained.

lemma ConsecutiveEven(k: int)
  requires k >= 0
  ensures (k * (k + 1)) % 2 == 0
  decreases k
{
  if k > 0 {
    ConsecutiveEven(k - 1);
    assert k * (k + 1) == (k - 1) * k + 2 * k;
  }
}

lemma GaussStep(i: int)
  requires i >= 1
  ensures PyFloorDiv((i - 1) * i, 2) + i == PyFloorDiv(i * (i + 1), 2)
{
  ConsecutiveEven(i - 1);
  var k := PyFloorDiv((i - 1) * i, 2);
  assert (i - 1) * i == 2 * k;
  assert i * (i + 1) == (i - 1) * i + 2 * i == 2 * (k + i);
}
