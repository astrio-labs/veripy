"""Explicit Werkzeug ETag regex and value dependency models.

The regex model requires no LF (HTTP field lines); arbitrary re remains rejected.
ETags models constructor state as sets, without object identity or iteration order.
"""
import ast
PATTERN=r'([Ww]/)?(?:"(.*?)"|(.*?))(?:\s*,\s*|$)'
PREAMBLE=r'''
datatype VHttpMatch = VHttpMatched(VHttpWeak: PyOpt<string>, VHttpQuoted: PyOpt<string>, VHttpRaw: PyOpt<string>, VHttpEnd: int)
datatype VHttpETags = VHttpTags(VHttpStrong: set<PyOpt<string>>, VHttpWeaks: set<PyOpt<string>>, VHttpStar: bool)
function VHttpSpaces(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures i <= VHttpSpaces(s,i) <= |s|
  decreases |s|-i
{ if i < |s| && VUnicodeSpace(s[i]) then VHttpSpaces(s,i+1) else i }
function VHttpDelimiter(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures VHttpDelimiter(s,i) == -1 || i <= VHttpDelimiter(s,i) <= |s|
{
  var j := VHttpSpaces(s,i);
  if j < |s| && s[j] == ',' then VHttpSpaces(s,j+1)
  else if i == |s| then i else -1
}
function VHttpRawStop(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures i <= VHttpRawStop(s,i) <= |s|
  ensures VHttpDelimiter(s,VHttpRawStop(s,i)) >= 0
  decreases |s|-i
{ if VHttpDelimiter(s,i) >= 0 then i else VHttpRawStop(s,i+1) }
function VHttpQuoteStop(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures VHttpQuoteStop(s,i) == -1 || i <= VHttpQuoteStop(s,i) < |s|
  ensures VHttpQuoteStop(s,i) != -1 ==> VHttpDelimiter(s,VHttpQuoteStop(s,i)+1) >= 0
  decreases |s|-i
{ if i == |s| then -1 else if s[i] == '"' && VHttpDelimiter(s,i+1) >= 0 then i else VHttpQuoteStop(s,i+1) }
function VHttpMatchAt(s: string, p: int): PyOpt<VHttpMatch>
  requires 0 <= p <= |s| && PyStrFind(s,"\n") < 0
  ensures VHttpMatchAt(s,p).PySome?
  ensures p <= VHttpMatchAt(s,p).v.VHttpEnd <= |s|
  ensures p < |s| ==> p < VHttpMatchAt(s,p).v.VHttpEnd
{
  var weak := p+2 <= |s| && (s[p..p+2] == "W/" || s[p..p+2] == "w/");
  var i := if weak then p+2 else p;
  var q := if i < |s| && s[i] == '"' then VHttpQuoteStop(s,i+1) else -1;
  var raw := VHttpRawStop(s,i);
  var w := if weak then PySome(s[p..p+2]) else PyNone;
  if q >= 0 then PySome(VHttpMatched(w,PySome(s[i+1..q]),PyNone,VHttpDelimiter(s,q+1)))
  else PySome(VHttpMatched(w,PyNone,PySome(s[i..raw]),VHttpDelimiter(s,raw)))
}
function VHttpTagSet(xs: seq<PyOpt<string>>): set<PyOpt<string>> { set x | x in xs }
'''


def call_model(encoder,node):
    from .encoder import _err
    f=node.func
    if not isinstance(f,ast.Attribute):return None
    dtype=encoder._infer(f.value) if not isinstance(f.value,ast.Name) or f.value.id in encoder.types else None
    if dtype=='PyOpt<VHttpMatch>':
        if node.args or node.keywords or f.attr not in {'groups','end'}:raise _err(node,'ETag matches expose only groups() and end()')
        value=f'({encoder.expr(f.value)}).v'
        if f.attr=='end':return 'int',value+'.VHttpEnd'
        return '(PyOpt<string>, PyOpt<string>, PyOpt<string>)',f'({value}.VHttpWeak, {value}.VHttpQuoted, {value}.VHttpRaw)'
    if isinstance(f.value,ast.Name) and f.value.id=='ds' and f.attr=='ETags':
        if not any(m['kind']=='etag' for m in encoder.regex_models.values()) or 'ds' in encoder._shadowed:
            raise _err(node,'ETags constructor requires the explicit Werkzeug dependency model')
        if len(node.args)>2 or any(k.arg!='star_tag' for k in node.keywords) or len(node.keywords)>1:raise _err(node,'ETags constructor supports strong/weak sequences and star_tag')
        values=[]
        for arg in node.args:
            dtype=encoder._infer(arg)
            if dtype not in {'seq<PyOpt<string>>','seq<string>'}:raise _err(node,'ETags requires owned scalar string/None sequences')
            value=encoder.expr(arg)
            if dtype=='seq<string>':value=f'seq(|{value}|, i => PySome({value}[i]))'
            values.append(f'VHttpTagSet({value})')
        values+=['{}']*(2-len(values))
        star=encoder._coerce(node.keywords[0].value,'bool') if node.keywords else 'false'
        return 'VHttpETags',f'VHttpTags((if {star} then {{}} else {values[0]}), {values[1]}, {star})'
    return None

PREAMBLE += r'''
function VHttpEmpty(star: bool): VHttpETags { VHttpTags({},{},star) }
function VHttpFromSeq(strong: seq<PyOpt<string>>, weak: seq<PyOpt<string>>): VHttpETags { VHttpTags(VHttpTagSet(strong),VHttpTagSet(weak),false) }
function VHttpAddStrong(state: VHttpETags, value: PyOpt<string>): VHttpETags { VHttpTags(state.VHttpStrong+{value},state.VHttpWeaks,false) }
function VHttpAddWeak(state: VHttpETags, value: PyOpt<string>): VHttpETags { VHttpTags(state.VHttpStrong,state.VHttpWeaks+{value},false) }
'''


def _constructor_model(self, strong_etags=None, weak_etags=None, star_tag=False):
    if not star_tag and strong_etags:
        self._strong = frozenset(strong_etags)
    else:
        self._strong = frozenset()
    self._weak = frozenset(weak_etags or ())
    self.star_tag = star_tag


def guard_dependency(function):
    import builtins
    from abc import ABCMeta
    from veripy.guards.runtime import PreconditionError
    module=function.__globals__.get('ds')
    cls=getattr(module,'ETags',None)
    def signature(fn):
        code=getattr(fn,'__code__',None)
        return None if code is None else (code.co_code,code.co_consts,code.co_names,code.co_varnames,code.co_argcount,code.co_kwonlyargcount)
    valid=(type(cls) is ABCMeta and type(cls).__call__ is type.__call__
           and type(cls).__getattribute__ is type.__getattribute__ and cls.__getattribute__ is object.__getattribute__
           and cls.__new__ is object.__new__ and cls.__setattr__ is object.__setattr__
           and signature(cls.__init__)==signature(_constructor_model)
           and cls.__init__.__defaults__==(None,None,False)
           and cls.__init__.__globals__.get('frozenset',builtins.frozenset) is builtins.frozenset
           and not any(name in base.__dict__ for base in cls.__mro__ for name in ['_strong','_weak','star_tag']))
    if not valid:raise PreconditionError(function.__name__,'Werkzeug ETags constructor dependency changed')
