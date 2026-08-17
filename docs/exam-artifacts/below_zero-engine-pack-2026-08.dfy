lemma PySumSnoc(s: seq<int>, x: int)
  ensures PySum(s + [x]) == PySum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    PySumSnoc(s[1..], x);
  }
}

lemma SliceSnoc(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures PySum(PySlice(s, 0, i + 1)) == PySum(PySlice(s, 0, i)) + s[i]
{
  assert PySlice(s, 0, i + 1) == PySlice(s, 0, i) + [s[i]];
  PySumSnoc(PySlice(s, 0, i), s[i]);
}
