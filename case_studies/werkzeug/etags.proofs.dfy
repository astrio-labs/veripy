function VHttpUnquote(s: string): (PyOpt<string>,PyOpt<bool>) {
  var stripped := VUnicodeStrip(s);
  var weak := PyStrStartsWith(stripped,"W/") || PyStrStartsWith(stripped,"w/");
  var value := if weak then PySlice(stripped,2,|stripped|) else stripped;
  var quoted := PySlice(value,0,1) == "\"" && PySlice(value,-1,|value|) == "\"";
  (PySome(if quoted then PySlice(value,1,-1) else value),PySome(weak))
}
predicate VHttpUnquoteCorrect(s: PyOpt<string>, r: (PyOpt<string>,PyOpt<bool>)) {
  r == (if s.PyNone? || |s.v| == 0 then (PyNone,PyNone) else VHttpUnquote(s.v))
}
function VHttpParse(s: string, p: int, state: VHttpETags): VHttpETags
  requires PyStrFind(s,"\n") < 0 && 0 <= p <= |s|
  decreases |s|-p
{
  if p == |s| then state
  else
    var m := VHttpMatchAt(s,p).v;
    var raw := if m.VHttpQuoted.PySome? && |m.VHttpQuoted.v| > 0 then m.VHttpQuoted else m.VHttpRaw;
    if m.VHttpRaw == PySome("*") then VHttpEmpty(true)
    else if m.VHttpWeak.PySome? && |m.VHttpWeak.v| > 0 then VHttpParse(s,m.VHttpEnd,VHttpAddWeak(state,raw))
    else VHttpParse(s,m.VHttpEnd,VHttpAddStrong(state,raw))
}
predicate VHttpParsedCorrect(s: PyOpt<string>, r: VHttpETags)
  requires s.PyNone? || PyStrFind(s.v,"\n") < 0
{
  r == (if s.PyNone? || |s.v| == 0 then VHttpEmpty(false) else VHttpParse(s.v,0,VHttpEmpty(false)))
}
predicate VHttpParseInvariant(s: PyOpt<string>, p: int, strong: seq<PyOpt<string>>, weak: seq<PyOpt<string>>)
  requires s.PySome? && PyStrFind(s.v,"\n") < 0 && 0 <= p <= |s.v|
{
  VHttpParse(s.v,p,VHttpFromSeq(strong,weak)) == VHttpParse(s.v,0,VHttpEmpty(false))
}
lemma VHttpSetEmpty()
  ensures VHttpFromSeq([],[]) == VHttpEmpty(false)
{}
lemma VHttpSetStep(strong: seq<PyOpt<string>>, weak: seq<PyOpt<string>>, raw: PyOpt<string>)
  ensures VHttpFromSeq(strong+[raw],weak) == VHttpAddStrong(VHttpFromSeq(strong,weak),raw)
  ensures VHttpFromSeq(strong,weak+[raw]) == VHttpAddWeak(VHttpFromSeq(strong,weak),raw)
{}

predicate VHttpQuoteCorrect(s: string, weak: bool, result: string, error: bool) {
  error == (PyStrFind(s,"\"") >= 0) && (!error ==> result == (if weak then "W/" else "") + "\"" + s + "\"")
}
