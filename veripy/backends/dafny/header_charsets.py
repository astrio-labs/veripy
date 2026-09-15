"""Closed capture model for Werkzeug's ASCII extended-header value pattern."""
import ast

PATTERN = "\n    ([\\w!#$%&*+\\-.^`|~]*)'  # charset part, could be empty\n    [\\w!#$%&*+\\-.^`|~]*'  # don't care about language part, usually empty\n    ([\\w!#$%&'*+\\-.^`|~]+)  # one or more token chars with percent encoding\n    "
FLAGS = 320  # re.ASCII | re.VERBOSE
PREAMBLE = r'''
datatype VCharsetCapture = VCharsetCaptured(VCharsetEncoding: string, VCharsetValue: string)
predicate VCharsetToken(c: char, value: bool) {
  'a' <= c <= 'z' || 'A' <= c <= 'Z' || '0' <= c <= '9' ||
  c in "_!#$%&*+-.^`|~" || (value && c == '\'')
}
function VCharsetEnd(s: string, i: int, value: bool): int
  requires 0 <= i <= |s|
  ensures i <= VCharsetEnd(s,i,value) <= |s|
  ensures forall j :: i <= j < VCharsetEnd(s,i,value) ==> VCharsetToken(s[j],value)
  decreases |s| - i
{ if i < |s| && VCharsetToken(s[i],value) then VCharsetEnd(s,i+1,value) else i }
function VCharsetMatch(s: string): PyOpt<VCharsetCapture>
  ensures VCharsetMatch(s).PySome? ==> |VCharsetMatch(s).v.VCharsetValue| > 0
  ensures VCharsetMatch(s).PySome? ==> |VCharsetMatch(s).v.VCharsetValue| <= |s|
  ensures VCharsetMatch(s).PySome? ==> (forall i :: 0 <= i < |VCharsetMatch(s).v.VCharsetValue| ==> VCharsetMatch(s).v.VCharsetValue[i] as int < 128)
{
  var a := VCharsetEnd(s,0,false);
  if a == |s| || s[a] != '\'' then PyNone else
  var b := VCharsetEnd(s,a+1,false);
  if b == |s| || s[b] != '\'' then PyNone else
  var c := VCharsetEnd(s,b+1,true);
  if c == b+1 then PyNone else PySome(VCharsetCaptured(s[..a],s[b+1..c]))
}
'''
NAMES=frozenset({'VCharsetCapture','VCharsetCaptured','VCharsetEncoding','VCharsetValue','VCharsetToken','VCharsetEnd','VCharsetMatch'})

def call_model(encoder,node):
    from veripy.backends.dafny.encoder import _err
    f=node.func
    if not isinstance(f,ast.Attribute):return None
    dtype=encoder._infer(f.value) if not isinstance(f.value,ast.Name) or f.value.id in encoder.types else None
    if dtype=='PyOpt<VCharsetCapture>':
        if f.attr!='groups' or node.args or node.keywords:
            raise _err(node,'charset matches expose only groups() without a default')
        value=f'({encoder.expr(f.value)}).v'
        return '(string, string)',f'({value}.VCharsetEncoding, {value}.VCharsetValue)'
    if not isinstance(f.value,ast.Name):return None
    model=encoder.regex_models.get(f.value.id)
    if not model or model['kind']!='charset':return None
    if f.value.id in encoder._shadowed or f.attr!='match' or len(node.args)!=1 or node.keywords or encoder._infer(node.args[0])!='string':
        raise _err(node,'charset pattern requires unshadowed match(string)')
    return 'PyOpt<VCharsetCapture>',f'VCharsetMatch({encoder.expr(node.args[0])})'
