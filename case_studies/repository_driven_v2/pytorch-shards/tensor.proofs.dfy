lemma ProductStep(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures PyProd(PySlice(s, 0, i + 1)) == PyProd(PySlice(s, 0, i)) * s[i]
{
  assert PySlice(s, 0, i + 1) == s[..i + 1];
  assert PySlice(s, 0, i) == s[..i];
  assert s[..i + 1][..i] == s[..i];
}

lemma FullProduct(s: seq<int>)
  ensures PyProd(PySlice(s, 0, |s|)) == PyProd(s)
{ assert PySlice(s, 0, |s|) == s; }

lemma SumExtension(a: seq<int>, b: seq<int>)
  requires |a| == |b| + 1
  requires forall j :: 0 <= j < |b| ==> a[j] == b[j]
  ensures PySum(a) == PySum(b) + a[|b|]
{ assert a[..|b|] == b; }
