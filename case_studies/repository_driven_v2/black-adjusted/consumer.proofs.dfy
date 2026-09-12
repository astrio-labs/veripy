lemma SortedPairs(lines: seq<(int,int)>)
  ensures |PySorted2(lines)| == |lines|
  ensures forall x :: x in PySorted2(lines) <==> x in lines
{
  PySorted2Facts(lines);
}
