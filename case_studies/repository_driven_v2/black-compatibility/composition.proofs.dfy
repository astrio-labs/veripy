// Total sequence specification: preserves duplicate ranges, order and filtering.
function Find(ms: seq<VRec_LinesMapping>, x: int, lo: int): int
  requires 0 <= lo <= |ms|
  ensures lo <= Find(ms,x,lo) <= |ms|
  decreases |ms|-lo
{
  if lo == |ms| then lo
  else if ms[lo].vfieldoriginal_start <= x <= ms[lo].vfieldoriginal_end then lo
  else Find(ms,x,lo+1)
}

function Emit(ms: seq<VRec_LinesMapping>, lr: (int,int), si: int, ei: int): seq<(int,int)>
  requires 0 <= si <= ei <= |ms|
{
  if si == |ms| || ei == |ms| then [] else
  var sm := ms[si]; var em := ms[ei];
  var a := if sm.vfieldis_changed_block then sm.vfieldmodified_start else lr.0-sm.vfieldoriginal_start+sm.vfieldmodified_start;
  var b := if em.vfieldis_changed_block then em.vfieldmodified_end else lr.1-em.vfieldoriginal_start+em.vfieldmodified_start;
  if a <= b then [(a,b)] else []
}

function State(ls: seq<(int,int)>, ms: seq<VRec_LinesMapping>, n: int): (int,seq<(int,int)>)
  requires 0 <= n <= |ls|
  ensures 0 <= State(ls,ms,n).0 <= |ms|
  decreases n
{
  if n == 0 then (0,[]) else
  var prev := State(ls,ms,n-1);
  var si := Find(ms,ls[n-1].0,prev.0);
  var ei := Find(ms,ls[n-1].1,si);
  (si,prev.1 + Emit(ms,ls[n-1],si,ei))
}

function Expected(lines: seq<(int,int)>, ms: seq<VRec_LinesMapping>): seq<(int,int)>
{ State(PySorted2(lines),ms,|PySorted2(lines)|).1 }

predicate Progress(ls: seq<(int,int)>, ms: seq<VRec_LinesMapping>, n: int, cursor: int, output: seq<(int,int)>)
{ 0 <= n <= |ls| && State(ls,ms,n) == (cursor,output) }

lemma LookupExact(ms: seq<VRec_LinesMapping>, x: int, lo: int, index: int)
  requires 0 <= lo <= index <= |ms|
  requires index < |ms| ==> ms[index].vfieldoriginal_start <= x <= ms[index].vfieldoriginal_end
  requires forall k :: lo <= k < index ==> !(ms[PyIndex(k,|ms|)].vfieldoriginal_start <= x <= ms[PyIndex(k,|ms|)].vfieldoriginal_end)
  ensures index == Find(ms,x,lo)
  decreases index-lo
{ if lo < index { assert PyIndex(lo,|ms|) == lo; assert !(ms[PyIndex(lo,|ms|)].vfieldoriginal_start <= x <= ms[PyIndex(lo,|ms|)].vfieldoriginal_end); LookupExact(ms,x,lo+1,index); } }

lemma Advance(ls: seq<(int,int)>, ms: seq<VRec_LinesMapping>, n: int, cursor: int, output: seq<(int,int)>, si: int, ei: int)
  requires 0 <= n < |ls|
  requires Progress(ls,ms,n,cursor,output)
  requires cursor <= si <= ei <= |ms|
  requires si < |ms| ==> ms[si].vfieldoriginal_start <= ls[n].0 <= ms[si].vfieldoriginal_end
  requires ei < |ms| ==> ms[ei].vfieldoriginal_start <= ls[n].1 <= ms[ei].vfieldoriginal_end
  requires forall k :: cursor <= k < si ==> !(ms[PyIndex(k,|ms|)].vfieldoriginal_start <= ls[n].0 <= ms[PyIndex(k,|ms|)].vfieldoriginal_end)
  requires forall k :: si <= k < ei ==> !(ms[PyIndex(k,|ms|)].vfieldoriginal_start <= ls[n].1 <= ms[PyIndex(k,|ms|)].vfieldoriginal_end)
  ensures Progress(ls,ms,n+1,si,output+Emit(ms,ls[n],si,ei))
  ensures State(ls,ms,n+1) == (si,output+Emit(ms,ls[n],si,ei))
  ensures Emit(ms,ls[n],si,ei) == [] ==> Progress(ls,ms,n+1,si,output)
  ensures forall pair: (int,int) :: Emit(ms,ls[n],si,ei) == [pair] ==> Progress(ls,ms,n+1,si,output+[pair])
{
  LookupExact(ms,ls[n].0,cursor,si);
  LookupExact(ms,ls[n].1,si,ei);
  assert State(ls,ms,n+1) == (si,output+Emit(ms,ls[n],si,ei));
  if Emit(ms,ls[n],si,ei) == [] {
    assert output+Emit(ms,ls[n],si,ei) == output;
    assert State(ls,ms,n+1) == (si,output);
  }
}

lemma SortedPairs(lines: seq<(int,int)>)
  ensures |PySorted2(lines)| == |lines|
  ensures forall x :: x in PySorted2(lines) <==> x in lines
{ PySorted2Facts(lines); }

// The call immediately before the sole consumer return checks this exact
// postcondition. It is proof-only and never substituted for a runtime guard.
lemma Complete(lines: seq<(int,int)>, ms: seq<VRec_LinesMapping>, cursor: int, output: seq<(int,int)>)
  requires Progress(PySorted2(lines),ms,|PySorted2(lines)|,cursor,output)
  ensures output == Expected(lines,ms)
{}

lemma ExposeEmit(ms: seq<VRec_LinesMapping>, lr: (int,int), si: int, ei: int, a: int, b: int)
  requires 0 <= si <= ei < |ms|
  requires a == (if ms[si].vfieldis_changed_block then ms[si].vfieldmodified_start else lr.0-ms[si].vfieldoriginal_start+ms[si].vfieldmodified_start)
  requires b == (if ms[ei].vfieldis_changed_block then ms[ei].vfieldmodified_end else lr.1-ms[ei].vfieldoriginal_start+ms[ei].vfieldmodified_start)
  ensures Emit(ms,lr,si,ei) == (if a <= b then [(a,b)] else [])
{}

lemma ExposeEmpty(ms: seq<VRec_LinesMapping>, lr: (int,int), si: int, ei: int)
  requires 0 <= si <= ei <= |ms|
  requires si == |ms| || ei == |ms|
  ensures Emit(ms,lr,si,ei) == []
{}

lemma CheckNext(ls: seq<(int,int)>, ms: seq<VRec_LinesMapping>, n: int, cursor: int, output: seq<(int,int)>)
  requires Progress(ls,ms,n,cursor,output)
  ensures Progress(ls,ms,n,cursor,output)
{}

lemma PairEta(ls: seq<(int,int)>, n: int, a: int, b: int)
  requires 0 <= n < |ls|
  requires ls[n].0 == a && ls[n].1 == b
  ensures ls[n] == (a,b)
{}

function MappingChunk(bs: seq<VRecMatch>, i: int): seq<VRec_LinesMapping>
  requires 0 <= i < |bs|
{
  var b := bs[i];
  var gap := if i == 0 then
    (if b.vfielda != 0 || b.vfieldb != 0 then [VMake_LinesMapping(1,b.vfielda,1,b.vfieldb,false)] else [])
    else [VMake_LinesMapping(bs[i-1].vfielda+bs[i-1].vfieldsize+1,b.vfielda,bs[i-1].vfieldb+bs[i-1].vfieldsize+1,b.vfieldb,true)];
  gap + (if i < |bs|-1 then [VMake_LinesMapping(b.vfielda+1,b.vfielda+b.vfieldsize,b.vfieldb+1,b.vfieldb+b.vfieldsize,false)] else [])
}

function MappingPrefix(bs: seq<VRecMatch>, n: int): seq<VRec_LinesMapping>
  requires 0 <= n <= |bs|
  decreases n
{ if n == 0 then [] else MappingPrefix(bs,n-1)+MappingChunk(bs,n-1) }

predicate MappingProgress(bs: seq<VRecMatch>, n: int, output: seq<VRec_LinesMapping>)
{ 0 <= n <= |bs| && output == MappingPrefix(bs,n) }

lemma MappingStep(bs: seq<VRecMatch>, i: int, output: seq<VRec_LinesMapping>)
  requires 0 <= i < |bs|
  requires MappingProgress(bs,i,output)
  ensures MappingProgress(bs,i+1,output+MappingChunk(bs,i))
  ensures MappingPrefix(bs,i+1) == output+MappingChunk(bs,i)
{}

lemma MappingComplete(bs: seq<VRecMatch>, output: seq<VRec_LinesMapping>)
  requires MappingProgress(bs,|bs|,output)
  ensures output == MappingPrefix(bs,|bs|)
{}

lemma Composition(lines: seq<(int,int)>, blocks: seq<VRecMatch>, mappings: seq<VRec_LinesMapping>, output: seq<(int,int)>)
  requires mappings == MappingPrefix(blocks,|blocks|)
  requires output == Expected(lines,mappings)
  ensures output == Expected(lines,MappingPrefix(blocks,|blocks|))
{}
