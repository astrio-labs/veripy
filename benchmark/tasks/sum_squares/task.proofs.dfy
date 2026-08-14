// A sum of nonnegative elements is nonnegative -- inductive over PySum's
// snoc recursion, which Z3 will not find unaided. Invoked at the mapped
// seq ([x * x for x in values]), whose elements are squares.
lemma SumNonNeg(s: seq<int>)
  requires forall k | 0 <= k < |s| :: s[k] >= 0
  ensures PySum(s) >= 0
  decreases |s|
{
  if |s| > 0 {
    SumNonNeg(s[..|s|-1]);
  }
}
