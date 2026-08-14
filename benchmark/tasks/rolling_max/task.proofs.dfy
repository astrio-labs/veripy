// PySeqMax dominates every element -- inductive over the sequence length,
// which Z3 will not find unaided.
lemma SeqMaxDominates(s: seq<int>)
  requires |s| >= 1
  ensures forall j | 0 <= j < |s| :: s[j] <= PySeqMax(s)
{
  if |s| > 1 {
    SeqMaxDominates(s[..|s|-1]);
  }
}

// The prefix-closed form the rolling-max postcondition needs: every
// element of every prefix is dominated by that prefix's max.
lemma SeqMaxDominatesAll(s: seq<int>)
  ensures forall i, j | 0 <= j <= i < |s| :: s[j] <= PySeqMax(PySlice(s, 0, i + 1))
{
  forall i | 0 <= i < |s|
    ensures forall j | 0 <= j <= i :: s[j] <= PySeqMax(PySlice(s, 0, i + 1))
  {
    assert PySlice(s, 0, i + 1) == s[..i + 1];
    SeqMaxDominates(s[..i + 1]);
  }
}
