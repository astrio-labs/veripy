"""Closed ASCII percent decoding with four replacement codecs.

The Dafny functions are checked definitions. Correspondence to the pinned
CPython dependency is reviewed and tested, not a mechanized interpreter theorem.
"""
import ast

PREAMBLE = r'''
predicate VPercentASCII(s: string) { forall i :: 0 <= i < |s| ==> s[i] as int < 128 }
predicate VPercentBytes(b: seq<int>) { forall i :: 0 <= i < |b| ==> 0 <= b[i] < 256 }
predicate VPercentEncoding(e: string) { e in {"ascii", "us-ascii", "utf-8", "iso-8859-1"} }
function VPercentHex(c: char): int
  ensures -1 <= VPercentHex(c) < 16
{
  if '0' <= c <= '9' then c as int - 48
  else if 'a' <= c <= 'f' then c as int - 87
  else if 'A' <= c <= 'F' then c as int - 55 else -1
}
function VPercentScan(s: string): seq<int>
  requires VPercentASCII(s)
  ensures VPercentBytes(VPercentScan(s))
  ensures |VPercentScan(s)| <= |s|
  decreases |s|
{
  if |s| == 0 then []
  else if |s| >= 3 && s[0] == '%' && VPercentHex(s[1]) >= 0 && VPercentHex(s[2]) >= 0
    then [16*VPercentHex(s[1])+VPercentHex(s[2])] + VPercentScan(s[3..])
  else [s[0] as int] + VPercentScan(s[1..])
}
predicate VPercentCont(b: int) { 128 <= b <= 191 }
function VPercentWidth(h: int): int {
  if 194 <= h <= 223 then 2 else if 224 <= h <= 239 then 3 else if 240 <= h <= 244 then 4 else 0
}
predicate VPercentSecond(h: int, b: int) {
  (if h == 224 then 160 else if h == 240 then 144 else 128) <= b <=
  (if h == 237 then 159 else if h == 244 then 143 else 191)
}
function VPercentUtfStep(b: seq<int>): (int, int)
  requires VPercentBytes(b) && |b| > 0
  ensures 1 <= VPercentUtfStep(b).0 <= |b|
  ensures 0 <= VPercentUtfStep(b).1 <= 1114111
  ensures !(55296 <= VPercentUtfStep(b).1 <= 57343)
{
  var h := b[0]; var w := VPercentWidth(h);
  if h < 128 then (1,h)
  else if w == 0 || |b| < 2 || !VPercentSecond(h,b[1]) then (1,65533)
  else if w == 2 then (2,(h-192)*64+b[1]-128)
  else if |b| < 3 || !VPercentCont(b[2]) then (2,65533)
  else if w == 3 then (3,(h-224)*4096+(b[1]-128)*64+b[2]-128)
  else if |b| < 4 || !VPercentCont(b[3]) then (3,65533)
  else (4,(h-240)*262144+(b[1]-128)*4096+(b[2]-128)*64+b[3]-128)
}
function VPercentDecode(b: seq<int>, e: string): string
  requires VPercentBytes(b) && VPercentEncoding(e)
  ensures |VPercentDecode(b,e)| <= |b|
  decreases |b|
{
  if |b| == 0 then ""
  else if e == "utf-8" then
    var step := VPercentUtfStep(b);
    [step.1 as char] + VPercentDecode(b[step.0..],e)
  else [(if e == "iso-8859-1" || b[0] < 128 then b[0] else 65533) as char] + VPercentDecode(b[1..],e)
}
lemma VPercentPlain(s: string, e: string)
  requires VPercentASCII(s) && VPercentEncoding(e)
  ensures '%' !in s ==> VPercentDecode(VPercentScan(s),e) == s
  decreases |s|
{
  if |s| > 0 && '%' !in s {
    VPercentPlain(s[1..],e);
    assert VPercentScan(s) == [s[0] as int] + VPercentScan(s[1..]);
    assert VPercentUtfStep(VPercentScan(s)) == (1,s[0] as int);
  }
}
function VPercentUnquote(s: string, e: string): string
  requires VPercentASCII(s) && VPercentEncoding(e)
  ensures |VPercentUnquote(s,e)| <= |s|
  ensures '%' !in s ==> VPercentUnquote(s,e) == s
{ VPercentPlain(s,e); VPercentDecode(VPercentScan(s),e) }
'''
NAMES = frozenset({'VPercentASCII','VPercentBytes','VPercentEncoding','VPercentHex',
    'VPercentScan','VPercentCont','VPercentWidth','VPercentSecond','VPercentUtfStep',
    'VPercentDecode','VPercentPlain','VPercentUnquote'})


def imports(module):
    names = {}
    for node in module.body:
        if isinstance(node, ast.ImportFrom) and node.module == 'urllib.parse' and not node.level:
            for alias in node.names:
                if alias.name == 'unquote':
                    name = alias.asname or alias.name
                    if name in names:
                        raise ValueError('percent-decoder import is repeated')
                    names[name] = node
    for name, original in names.items():
        for node in ast.walk(module):
            if isinstance(node, (ast.Import, ast.ImportFrom)) and node is not original:
                if any((a.asname or a.name.split('.')[0]) == name or a.name == '*' for a in node.names):
                    raise ValueError('percent-decoder import is rebound')
            if ((isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id == name)
                or (isinstance(node, ast.arg) and node.arg == name)
                or (isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name == name)):
                raise ValueError('percent-decoder dependency is shadowed or rebound')
        if sum((a.asname or a.name) == name for a in original.names) != 1:
            raise ValueError('percent-decoder import is ambiguous')
    return frozenset(names)


def call_model(encoder, node):
    if isinstance(node.func, ast.Attribute) and node.func.attr == 'isascii' and encoder._infer(node.func.value) == 'string':
        from veripy.backends.dafny.encoder import _err
        if node.args or node.keywords:
            raise _err(node, 'str.isascii requires no arguments')
        value = encoder.expr(node.func.value)
        index = encoder._fresh('ascii_index')
        return 'bool', f'(forall {index} :: 0 <= {index} < |{value}| ==> {value}[{index}] as int < 128)'
    if not isinstance(node.func, ast.Name) or node.func.id not in encoder.percent_names:
        return None
    from veripy.backends.dafny.encoder import _err
    if node.func.id in encoder._shadowed or len(node.args) != 1:
        raise _err(node, 'unquote model requires one positional ASCII string')
    if any(k.arg not in {'encoding', 'errors'} for k in node.keywords) or len({k.arg for k in node.keywords}) != len(node.keywords):
        raise _err(node, 'unquote model permits only encoding and errors keywords')
    keywords = {k.arg:k.value for k in node.keywords}
    encoding = keywords.get('encoding', ast.Constant(value='utf-8'))
    errors = keywords.get('errors', ast.Constant(value='replace'))
    if not isinstance(errors, ast.Constant) or errors.value != 'replace':
        raise _err(node, 'unquote model requires literal replacement error handling')
    if encoder._infer(node.args[0]) != 'string' or encoder._infer(encoding) != 'string':
        raise _err(node, 'unquote model requires string input and encoding')
    return 'string', f'VPercentUnquote({encoder.expr(node.args[0])}, {encoder.expr(encoding)})'


def guard_dependency(function, names):
    import builtins
    import _codecs
    import codecs
    import re
    from functools import wraps
    from types import CodeType, FunctionType, BuiltinFunctionType
    from veripy.backends.dafny import unquote_reference as reference
    from veripy.guards.runtime import PreconditionError

    def signature(fn):
        if type(fn) is not FunctionType or fn.__closure__ is not None:
            return None
        def code(c):
            return (c.co_code, tuple(code(v) if isinstance(v, CodeType) else v for v in c.co_consts),
                c.co_names, c.co_varnames, c.co_argcount, c.co_posonlyargcount, c.co_kwonlyargcount,
                c.co_flags, c.co_freevars, c.co_cellvars)
        return code(fn.__code__), fn.__defaults__, fn.__kwdefaults__

    expected = {name:signature(getattr(reference, name)) for name in
                ('unquote','_unquote_impl','_generate_unquoted_parts')}
    expected_hex = {(a+b).encode():bytes.fromhex(a+b) for a in reference._hexdig for b in reference._hexdig}
    builtin_values = {name:getattr(builtins,name) for name in ('isinstance','str','bytes','bytearray','len','KeyError')}
    pattern_type = type(re.compile(''))
    lookup_error, replace_errors = _codecs.lookup_error, codecs.replace_errors

    def valid(fn):
        if signature(fn) != expected['unquote']:
            return False
        namespace = fn.__globals__
        for name in ('_unquote_impl','_generate_unquoted_parts'):
            helper = namespace.get(name)
            if signature(helper) != expected[name] or helper.__globals__ is not namespace:
                return False
        for name, value in builtin_values.items():
            # Python functions retain their original builtins mapping even if
            # somebody later replaces the globals' __builtins__ entry.
            if namespace.get(name, fn.__builtins__.get(name)) is not value:
                return False
            for helper_name in ('_unquote_impl','_generate_unquoted_parts'):
                helper = namespace[helper_name]
                if namespace.get(name, helper.__builtins__.get(name)) is not value:
                    return False
        pattern, table = namespace.get('_asciire'), namespace.get('_hextobyte')
        return (type(pattern) is pattern_type and pattern.pattern == '([\x00-\x7f]+)' and pattern.flags == 32
            and type(namespace.get('_hexdig')) is str and namespace['_hexdig'] == reference._hexdig
            and (table is None or type(table) is dict and all(type(k) is bytes and type(v) is bytes for k,v in table.items()) and table == expected_hex)
            and type(replace_errors) is BuiltinFunctionType and replace_errors.__name__ == 'replace_errors'
            and replace_errors.__module__ is None and lookup_error('replace') is replace_errors)

    def checked(*args, **kwargs):
        if not all(valid(function.__globals__.get(name)) for name in names):
            raise PreconditionError(function.__name__, 'percent-decoder dependency changed')
        return function(*args, **kwargs)
    return wraps(function)(FunctionType(checked.__code__, function.__globals__, closure=checked.__closure__))


def guard_code(module, specs):
    names = imports(module)
    if not names:
        return ''
    return ('from veripy.backends.dafny.percent_decoding import guard_dependency as _veripy_guard_percent\n'
        + ''.join(f'{sp.name} = _veripy_guard_percent({sp.name}, {sorted(names)!r})\n' for sp in specs.functions))
