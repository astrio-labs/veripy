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
