// Slice-extension: extending a prefix by one element appends exactly that
// element -- the fact that steps every running-sum invariant. Z3 does not
// connect PySlice's clamped bounds to the snoc shape unaided.
lemma SliceSnoc(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures PySlice(s, 0, i + 1) == PySlice(s, 0, i) + [s[i]]
{
}
