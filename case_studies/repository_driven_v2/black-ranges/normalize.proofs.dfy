lemma FlattenStep(a: seq<seq<(int, int)>>, b: seq<seq<(int, int)>>)
  requires |b| == |a| + 1
  requires forall j :: 0 <= j < |a| ==> a[j] == b[j]
  ensures PyFlatten(b) == PyFlatten(a) + b[|a|]
{
  assert b[..|a|] == a;
}
