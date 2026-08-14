// ---- proof additions from task.proofs.dfy ----
lemma PyMaxDominates(s: seq<int>, m: int)
  requires 0 <= m < |s|
  ensures s[m] <= PySeqMax(s)
  decreases |s|
{
  if |s| == 1 {
  } else if m == 0 {
  } else {
    PyMaxDominates(s[1..], m - 1);
  }
}

lemma SeqMaxDominatesAll(numbers: seq<int>)
  ensures forall i, j :: 0 <= i < |numbers| && 0 <= j <= i ==> numbers[j] <= PySeqMax(numbers[..i + 1])
{
  forall i, j | 0 <= i < |numbers| && 0 <= j <= i
    ensures numbers[j] <= PySeqMax(numbers[..i + 1])
  {
    PyMaxDominates(numbers[..i + 1], j);
  }
}
