"""Finite CPython Unicode tables and the context-sensitive final-sigma rule.

Tables are generated from builtin str operations, never user modules. The full
scalar domain is retained; the model does not silently restrict strings to ASCII.
"""
import ast
from functools import lru_cache
import sys
import unicodedata

NAMES = frozenset({'VUnicodeLowerChar','VUnicodeCased','VUnicodeIgnorable',
                   'VUnicodeBefore','VUnicodeAfter','VUnicodeLowerAt','VUnicodeLower',
                   'VUnicodeSpace','VUnicodeLStrip','VUnicodeRStrip','VUnicodeStrip'})


def needed(module):
    if any(isinstance(n,ast.ImportFrom) and n.module=='urllib.request' and not n.level and any(a.name=='parse_http_list' for a in n.names) for n in module.body):return True
    return any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)
               and (n.func.attr=='compile' or n.func.attr=='lower' or n.func.attr in {'strip','lstrip','rstrip'} and not n.args)
               for n in ast.walk(module))


def ranges(values):
    result=[]
    for value in values:
        if result and result[-1][1]+1==value:result[-1]=(result[-1][0],value)
        else:result.append((value,value))
    return result


@lru_cache(maxsize=1)
def tables():
    lower={};cased=[];ignorable=[];space=[]
    for i in range(0x110000):
        if 0xD800<=i<=0xDFFF:continue
        c=chr(i)
        if c.lower()!=c:lower[i]=tuple(map(ord,c.lower()))
        # These builtin probes distinguish the two transitions relevant to
        # final sigma, including characters that are both cased and ignorable.
        if (c+'Σ').lower().endswith('ς'):cased.append(i)
        elif ('AΣ'+c+'A').lower()[1]=='σ':ignorable.append(i)
        if c.isspace():space.append(i)
    return lower,ranges(cased),ranges(ignorable),ranges(space)


def _predicate(items):
    if not items:return 'false'
    if len(items)==1:
        a,b=items[0]
        return f'{a} <= c as int <= {b}' if a!=b else f'c as int == {a}'
    mid=len(items)//2
    return f'({_predicate(items[:mid])}) || ({_predicate(items[mid:])})'


def _lower_tree(items):
    if not items:return '[c]'
    mid=len(items)//2;key,value=items[mid]
    text='['+', '.join(f'({i} as char)' for i in value)+']'
    return f'(if c as int == {key} then {text} else if c as int < {key} then {_lower_tree(items[:mid])} else {_lower_tree(items[mid+1:])})'


@lru_cache(maxsize=1)
def preamble():
    lower,cased,ignorable,space=tables()
    return f'''// CPython {sys.version_info.major}.{sys.version_info.minor}; Unicode {unicodedata.unidata_version}
function VUnicodeLowerChar(c: char): string {{ {_lower_tree(sorted(lower.items()))} }}
predicate VUnicodeCased(c: char) {{ {_predicate(cased)} }}
predicate VUnicodeIgnorable(c: char) {{ {_predicate(ignorable)} }}
predicate VUnicodeSpace(c: char) {{ {_predicate(space)} }}
function VUnicodeBefore(s: string, i: int): bool
  requires 0 <= i <= |s|
  decreases i
{{ i > 0 && (if VUnicodeIgnorable(s[i-1]) then VUnicodeBefore(s,i-1) else VUnicodeCased(s[i-1])) }}
function VUnicodeAfter(s: string, i: int): bool
  requires 0 <= i <= |s|
  decreases |s|-i
{{ i < |s| && (if VUnicodeIgnorable(s[i]) then VUnicodeAfter(s,i+1) else VUnicodeCased(s[i])) }}
function VUnicodeLowerAt(s: string, i: int): string
  requires 0 <= i <= |s|
  decreases |s|-i
{{ if i == |s| then "" else
   (if s[i] as int == 931 && VUnicodeBefore(s,i) && !VUnicodeAfter(s,i+1)
    then [(962 as char)] else VUnicodeLowerChar(s[i])) + VUnicodeLowerAt(s,i+1) }}
function VUnicodeLower(s: string): string {{ VUnicodeLowerAt(s,0) }}
function VUnicodeLStrip(s: string): string
  decreases |s|
{{ if |s| > 0 && VUnicodeSpace(s[0]) then VUnicodeLStrip(s[1..]) else s }}
function VUnicodeRStrip(s: string): string
  decreases |s|
{{ if |s| > 0 && VUnicodeSpace(s[|s|-1]) then VUnicodeRStrip(s[..|s|-1]) else s }}
function VUnicodeStrip(s: string): string {{ VUnicodeRStrip(VUnicodeLStrip(s)) }}
'''


def guard_unicode(function,expected):
    from functools import wraps
    from types import FunctionType
    from veripy.guards.runtime import PreconditionError
    version=lambda:(sys.version_info.major,sys.version_info.minor,unicodedata.unidata_version)
    def checked(*args,**kwargs):
        if version()!=expected:raise PreconditionError(function.__name__,'Unicode string model configuration changed')
        return function(*args,**kwargs)
    return wraps(function)(FunctionType(checked.__code__,function.__globals__,closure=checked.__closure__))


def guard_code(module,specs):
    if not needed(module):return ''
    version=(sys.version_info.major,sys.version_info.minor,unicodedata.unidata_version)
    return ('from veripy.backends.dafny.unicode_strings import guard_unicode as _veripy_guard_unicode\n'
            + ''.join(f'{sp.name} = _veripy_guard_unicode({sp.name}, {version!r})\n' for sp in specs.functions))
