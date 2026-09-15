function VPaeth(a: int, b: int, c: int): int {
  var p := a+b-c;
  var pa := PyAbs(p-a); var pb := PyAbs(p-b); var pc := PyAbs(p-c);
  if pa <= pb && pa <= pc then a else if pb <= pc then b else c
}
function VPredict(s: seq<int>, p: seq<int>, output: seq<int>, unit: int, k: int, paeth: bool): int
  requires 1 <= unit && |s| == |p| == |output| && 0 <= k < |output|
{
  var a := if k < unit then 0 else output[k-unit];
  var b := p[k];
  var c := if k < unit then 0 else p[k-unit];
  if paeth then VPaeth(a,b,c) else PyFloorDiv(a+b,2)
}
predicate VFilterPrefix(s: seq<int>, p: seq<int>, output: seq<int>, unit: int, end: int, paeth: bool)
  requires 1 <= unit && |s| == |p| == |output| && 0 <= end <= |output|
{
  forall k :: 0 <= k < end ==> output[k] == PyMod(s[k]+VPredict(s,p,output,unit,k,paeth),256)
}
predicate VFilterOutput(s: seq<int>, p: seq<int>, output: seq<int>, unit: int, paeth: bool)
  requires 1 <= unit && |s| == |p| == |output|
{ VFilterPrefix(s,p,output,unit,|output|,paeth) }
lemma VFilterAdvance(s: seq<int>, p: seq<int>, output: seq<int>, unit: int, end: int, paeth: bool)
  requires 1 <= unit && |s| == |p| == |output| && 0 <= end < |output|
  requires VFilterPrefix(s,p,output,unit,end,paeth)
  ensures VFilterPrefix(s,p,output[end := PyMod(s[end]+VPredict(s,p,output,unit,end,paeth),256)],unit,end+1,paeth)
{
  var next := output[end := PyMod(s[end]+VPredict(s,p,output,unit,end,paeth),256)];
  forall k | 0 <= k < end+1
    ensures next[k] == PyMod(s[k]+VPredict(s,p,next,unit,k,paeth),256)
  {
    if k < end {
      assert output[k] == PyMod(s[k]+VPredict(s,p,output,unit,k,paeth),256);
    }
    if k >= unit {
      assert k-unit < end;
      assert next[k-unit] == output[k-unit];
    }
    assert VPredict(s,p,next,unit,k,paeth) == VPredict(s,p,output,unit,k,paeth);
  }
}
