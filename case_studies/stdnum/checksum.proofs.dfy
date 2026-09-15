function LuhnDouble(x: int, n: int): int
  requires n > 1
{ PyFloorDiv(2*x,n) + PyMod(2*x,n) }
function LuhnDigits(s: string, a: string): seq<int>
  requires forall c :: c in s ==> PyStrFind(a,[c]) >= 0
  ensures |LuhnDigits(s,a)| == |s|
  ensures forall i :: 0 <= i < |s| ==> LuhnDigits(s,a)[i] == VChecksumIndex(a,[s[|s|-1-i]])
  decreases |s|
{ if |s| == 0 then [] else [VChecksumIndex(a,[s[|s|-1]])] + LuhnDigits(s[..|s|-1],a) }
// Mathematical alternating positional sum, from the rightmost digit.
function LuhnTotal(v: seq<int>, n: int): int
  requires n > 1
  decreases |v|
{ if |v| == 0 then 0 else if |v| == 1 then v[0]
  else v[0] + LuhnDouble(v[1],n) + LuhnTotal(v[2..],n) }
function LuhnDoubles(v: seq<int>, n: int): seq<int>
  requires n > 1
  ensures |LuhnDoubles(v,n)| == |v|
  ensures forall i :: 0 <= i < |v| ==> LuhnDoubles(v,n)[i] == LuhnDouble(v[i],n)
  decreases |v|
{ if |v| == 0 then [] else [LuhnDouble(v[0],n)] + LuhnDoubles(v[1..],n) }
predicate LuhnExact(s: string, a: string, r: int)
  requires |a| > 1
  requires forall c :: c in s ==> PyStrFind(a,[c]) >= 0
{ r == PyMod(LuhnTotal(LuhnDigits(s,a),|a|),|a|) }
lemma LuhnSumHead(v: seq<int>)
  requires |v| > 0
  ensures PySum(v) == v[0] + PySum(v[1..])
  decreases |v|
{
  if |v| > 1 {
    LuhnSumHead(v[..|v|-1]);
    assert v[1..][..|v|-2] == v[..|v|-1][1..];
  }
}
lemma LuhnSplit(v: seq<int>, n: int)
  requires n > 1
  ensures PySum(VChecksumStep(v,2)) + PySum(LuhnDoubles(VChecksumStep(v[PyMin(1,|v|)..],2),n)) == LuhnTotal(v,n)
  decreases |v|
{
  if |v| > 0 {
    LuhnSumHead(VChecksumStep(v,2));
    if |v| > 1 {
      LuhnSplit(v[2..],n);
      var odd := VChecksumStep(v[1..],2);
      LuhnSumHead(LuhnDoubles(odd,n));
      assert LuhnDoubles(odd,n)[1..] == LuhnDoubles(odd[1..],n);
      assert v[2..][PyMin(1,|v[2..]|)..] == v[1..][PyMin(2,|v[1..]|)..];
    }
  }
}
lemma LuhnBridge(s: string, a: string, values: VChecksumTuple<int>, doubled: VChecksumTuple<int>)
  requires |a| > 1
  requires forall c :: c in s ==> PyStrFind(a,[c]) >= 0
  requires |values.VChecksumValues| == |s|
  requires forall i :: 0 <= i < |s| ==> values.VChecksumValues[i] == VChecksumIndex(a,[s[|s|-1-i]])
  requires |doubled.VChecksumValues| == |VChecksumStride(values.VChecksumValues,1,|s|,2)|
  requires forall i :: 0 <= i < |doubled.VChecksumValues| ==> doubled.VChecksumValues[i] == LuhnDouble(VChecksumStride(values.VChecksumValues,1,|s|,2)[i],|a|)
  ensures PySum(VChecksumStride(values.VChecksumValues,0,|s|,2)) + PySum(doubled.VChecksumValues) == LuhnTotal(LuhnDigits(s,a),|a|)
{
  var v := values.VChecksumValues;
  var odd := VChecksumStride(v,1,|s|,2);
  assert v == LuhnDigits(s,a);
  assert doubled.VChecksumValues == LuhnDoubles(odd,|a|);
  assert PySlice(v,0,|s|) == v;
  assert PySlice(v,1,|s|) == v[PyMin(1,|v|)..];
  LuhnSplit(v,|a|);
}
