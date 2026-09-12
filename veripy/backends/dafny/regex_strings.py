"""Checked language models for the frozen Packaging name patterns.

Only match existence and separator substitution are modeled; no arbitrary regex
or capture object is treated as a verified dependency. In particular, preserve
both Python's terminal-newline anchor rule and the upstream lookahead placement.
"""
import ast
import copy
from dataclasses import dataclass
import re

from . import http_strings

PATTERNS = {
    http_strings.PATTERN: ("etag",False,0),
    r'[A-Z0-9]|[A-Z0-9][A-Z0-9._-]*[A-Z0-9]': ('validate',False,2),
    r'^([A-Z0-9]|[A-Z0-9][A-Z0-9._-]*[A-Z0-9])$': ('validate',True,2),
    r'[a-z0-9]|[a-z0-9]([a-z0-9-](?!--))*[a-z0-9]': ('normalized',False,0),
    r'^([a-z0-9]|[a-z0-9]([a-z0-9-](?!--))*[a-z0-9])$': ('normalized',True,0),
    r'[-_.]+': ('separators',False,0),
}
NAMES=frozenset({'VRegexNameChar','VRegexLowerChar','VRegexValidName','VRegexNormalizedName',
                 'VRegexAnchorText','VRegexSkipSeparators','VRegexSubSeparators','VRegexMatch','VRegexPresent'})


def declarations(module):
    """Remove only explicitly modeled re.compile declarations, retaining imports."""
    aliases={a.asname or 're' for n in module.body if isinstance(n,ast.Import) for a in n.names if a.name=='re'}
    bindings={};remaining=[];available=set()
    for node in module.body:
        if isinstance(node,ast.Import):
            available.update(a.asname or 're' for a in node.names if a.name=='re')
        if (isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name)
                and isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Attribute)
                and isinstance(node.value.func.value,ast.Name) and node.value.func.value.id in available
                and node.value.func.attr=='compile'):
            call=node.value
            if call.keywords or len(call.args) not in {1,2} or not isinstance(call.args[0],ast.Constant) or type(call.args[0].value) is not str:
                remaining.append(node);continue
            pattern=call.args[0].value
            flags=0
            if len(call.args)==2:
                flag=call.args[1]
                if not (isinstance(flag,ast.Attribute) and isinstance(flag.value,ast.Name) and flag.value.id in aliases and flag.attr=='IGNORECASE'):
                    remaining.append(node);continue
                flags=2
            if pattern not in PATTERNS or PATTERNS[pattern][2]!=flags:
                remaining.append(node);continue
            name=node.targets[0].id
            if name in bindings:raise ValueError('regex dependency is rebound')
            bindings[name]={'pattern':pattern,'flags':flags,'kind':PATTERNS[pattern][0],'anchored':PATTERNS[pattern][1]}
        else:remaining.append(node)
    if any(m['kind']=='etag' for m in bindings.values()):
        ds_imports=[n for n in module.body if isinstance(n,ast.ImportFrom) and n.module=='werkzeug' and not n.level and len(n.names)==1 and n.names[0].name=='datastructures' and n.names[0].asname=='ds']
        if len(ds_imports)!=1:raise ValueError('ETag model requires explicit Werkzeug datastructures as ds import')
        for n in module.body:
            if isinstance(n,(ast.Import,ast.ImportFrom)) and n not in ds_imports and any((a.asname or a.name.split('.')[0])=='ds' or a.name=='*' for a in n.names):raise ValueError('ETags dependency import is rebound')
            if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name=='ds':raise ValueError('ETags dependency definition is rebound')
        for n in ast.walk(module):
            if isinstance(n,ast.Name) and isinstance(n.ctx,(ast.Store,ast.Del)) and n.id=='ds' or isinstance(n,ast.arg) and n.arg=='ds':raise ValueError('ETags dependency is rebound')
    if bindings:
        for node in remaining:
            if isinstance(node,(ast.FunctionDef,ast.ClassDef)) and node.name in bindings:
                raise ValueError('definition replaces regex dependency')
            if isinstance(node,ast.FunctionDef):continue
            for n in ast.walk(node):
                if isinstance(n,ast.Name) and isinstance(n.ctx,(ast.Store,ast.Del)) and n.id in bindings:
                    raise ValueError('regex dependency is rebound')
                if isinstance(n,ast.alias) and (n.asname or n.name.split('.')[0]) in bindings:
                    raise ValueError('import replaces regex dependency')
        for node in module.body:
            if isinstance(node,(ast.Import,ast.ImportFrom)):
                for a in node.names:
                    bound=a.asname or a.name.split('.')[0]
                    if a.name=='*' or bound in aliases and not (isinstance(node,ast.Import) and a.name=='re'):
                        raise ValueError('import can replace regex module')
        # Replacing the re module itself before declarations would change compile.
        for node in module.body:
            if isinstance(node,(ast.Import,ast.ImportFrom)):continue
            if isinstance(node,ast.FunctionDef) and node.name not in aliases:continue
            for n in ast.walk(node):
                if isinstance(n,ast.Name) and isinstance(n.ctx,(ast.Store,ast.Del)) and n.id in aliases:
                    raise ValueError('re module is rebound')
                if isinstance(n,ast.Attribute) and isinstance(n.ctx,(ast.Store,ast.Del)):
                    raise ValueError('module attribute mutation invalidates regex dependency')
    return ast.Module(body=remaining,type_ignores=module.type_ignores),bindings


def call_model(encoder,node):
    http=http_strings.call_model(encoder,node)
    if http is not None:return http
    f=node.func
    if not (isinstance(f,ast.Attribute) and isinstance(f.value,ast.Name)
            and f.value.id not in encoder._shadowed and f.value.id in encoder.regex_models):return None
    model=encoder.regex_models[f.value.id]
    from .encoder import _err
    if node.keywords:raise _err(node,'regex model requires positional arguments')
    if model['kind']=='etag':
        if f.attr!='match' or len(node.args)!=2 or encoder._eff_type(node.args[0])!='string' or encoder._infer(node.args[1])!='int':
            raise _err(node,'ETag regex requires match(string, position)')
        return 'PyOpt<VHttpMatch>',f'VHttpMatchAt({encoder._deopt(node.args[0])}, {encoder.expr(node.args[1])})'
    if f.attr in {'match','fullmatch'} and model['kind'] in {'validate','normalized'}:
        if len(node.args)!=1 or encoder._infer(node.args[0])!='string':raise _err(node,'regex presence model requires one string')
        value=encoder.expr(node.args[0])
        if f.attr=='match' and not model['anchored']:
            predicate='VRegexNameChar' if model['kind']=='validate' else 'VRegexLowerChar'
            test=f'(|{value}| > 0 && {predicate}({value}[0]))'
        else:
            if f.attr=='match':value=f'VRegexAnchorText({value})'
            predicate='VRegexValidName' if model['kind']=='validate' else 'VRegexNormalizedName'
            test=f'{predicate}({value})'
        return 'PyOpt<VRegexMatch>',f'(if {test} then PySome(VRegexPresent) else PyNone)'
    if f.attr=='sub' and model['kind']=='separators':
        if (len(node.args)!=2 or not isinstance(node.args[0],ast.Constant) or node.args[0].value!='-'
                or encoder._infer(node.args[1])!='string'):raise _err(node,'separator substitution requires literal dash replacement and one string')
        return 'string',f'VRegexSubSeparators({encoder.expr(node.args[1])})'
    raise _err(node,'regex operation needs an explicit model; only checked name matching/substitution is available')


PREAMBLE=r'''
datatype VRegexMatch = VRegexPresent
predicate VRegexNameChar(c: char) {
  'a' <= c <= 'z' || 'A' <= c <= 'Z' || '0' <= c <= '9' ||
  c as int == 304 || c as int == 305 || c as int == 383 || c as int == 8490
}
predicate VRegexLowerChar(c: char) { 'a' <= c <= 'z' || '0' <= c <= '9' }
predicate VRegexValidName(s: string) {
  |s| > 0 && VRegexNameChar(s[0]) && VRegexNameChar(s[|s|-1]) &&
  (forall i :: 1 <= i < |s|-1 ==> VRegexNameChar(s[i]) || s[i] in "._-")
}
predicate VRegexNormalizedName(s: string) {
  |s| > 0 && VRegexLowerChar(s[0]) && VRegexLowerChar(s[|s|-1]) &&
  (forall i :: 1 <= i < |s|-1 ==> (VRegexLowerChar(s[i]) || s[i] == '-') &&
    !(i+2 < |s| && s[i+1] == '-' && s[i+2] == '-'))
}
function VRegexAnchorText(s: string): string {
  if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s
}
function VRegexSkipSeparators(s: string): string
  ensures |VRegexSkipSeparators(s)| <= |s|
  decreases |s|
{ if |s| > 0 && s[0] in "-_." then VRegexSkipSeparators(s[1..]) else s }
function VRegexSubSeparators(s: string): string
  decreases |s|
{ if |s| == 0 then "" else if s[0] in "-_."
  then "-" + VRegexSubSeparators(VRegexSkipSeparators(s[1..]))
  else [s[0]] + VRegexSubSeparators(s[1..]) }
'''


def guard_regex(function,expected):
    from functools import wraps
    from types import FunctionType
    from veripy.guards.runtime import PreconditionError
    pattern_type=type(re.compile(''))
    http_guard=http_strings.guard_dependency
    def checked(*args,**kwargs):
        if any(m['kind']=='etag' for m in expected.values()):http_guard(function)
        for name,model in expected.items():
            actual=function.__globals__.get(name)
            if type(actual) is not pattern_type or actual.pattern!=model['pattern'] or actual.flags!=(model['flags']|32):
                raise PreconditionError(function.__name__,'regex dependency changed: '+name)
        return function(*args,**kwargs)
    return wraps(function)(FunctionType(checked.__code__,function.__globals__,closure=checked.__closure__))


def guard_code(module,specs):
    _,models=declarations(module)
    if not models:return ''
    return ('from veripy.backends.dafny.regex_strings import guard_regex as _veripy_guard_regex\n'
            + ''.join(f'{sp.name} = _veripy_guard_regex({sp.name}, {models!r})\n' for sp in specs.functions))

PREAMBLE += http_strings.PREAMBLE
NAMES = NAMES | frozenset({"VHttpMatch","VHttpMatched","VHttpETags","VHttpTags","VHttpSpaces","VHttpDelimiter","VHttpRawStop","VHttpQuoteStop","VHttpMatchAt","VHttpTagSet","VHttpEmpty","VHttpFromSeq","VHttpAddStrong","VHttpAddWeak"})
