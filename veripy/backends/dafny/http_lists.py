"""Closed CPython parse_http_list model and callable provenance guard.

The Python state machine below follows CPython 3.12 urllib.request.parse_http_list.
Its mapping to the recursive Dafny model is a reviewed dependency model, checked
by native/compiled conformance, not a mechanized CPython interpreter theorem.
"""
import ast

PREAMBLE=r'''
function VHeaderRaw(s: string, part: string, quoted: bool, escaped: bool): seq<string>
  decreases |s|
{
  if |s| == 0 then (if |part| > 0 then [VUnicodeStrip(part)] else [])
  else if escaped then VHeaderRaw(s[1..],part+[s[0]],quoted,false)
  else if quoted then
    if s[0] == '\\' then VHeaderRaw(s[1..],part,true,true)
    else VHeaderRaw(s[1..],part+[s[0]],s[0] != '"',false)
  else if s[0] == ',' then [VUnicodeStrip(part)]+VHeaderRaw(s[1..],"",false,false)
  else VHeaderRaw(s[1..],part+[s[0]],s[0] == '"',false)
}
function VHeaderFields(s: string): seq<string> { VHeaderRaw(s,"",false,false) }
'''
NAMES=frozenset({'VHeaderRaw','VHeaderFields'})


def imports(module):
    names={}
    for n in module.body:
        if isinstance(n,ast.ImportFrom) and n.module=='urllib.request' and not n.level:
            for a in n.names:
                if a.name=='parse_http_list':names[a.asname or a.name]=n
    for name,original in names.items():
        for n in ast.walk(module):
            if isinstance(n,(ast.Import,ast.ImportFrom)) and n is not original:
                if any((a.asname or a.name.split('.')[0])==name or a.name=='*' for a in n.names):
                    raise ValueError('HTTP list dependency import is rebound')
            if isinstance(n,ast.Name) and isinstance(n.ctx,(ast.Store,ast.Del)) and n.id==name or isinstance(n,ast.arg) and n.arg==name or isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name==name:
                raise ValueError('HTTP list dependency is shadowed or rebound')
        if sum(a.asname==name or a.asname is None and a.name==name for a in original.names)!=1:
            raise ValueError('HTTP list dependency import is ambiguous')
    return frozenset(names)


def call_model(encoder,node):
    if not (isinstance(node.func,ast.Name) and node.func.id in getattr(encoder,'http_list_names',())):return None
    from veripy.backends.dafny.encoder import _err
    if node.func.id in encoder._shadowed or node.keywords or len(node.args)!=1 or encoder._infer(node.args[0])!='string':
        raise _err(node,'HTTP list parser requires one positional scalar string and its unshadowed dependency')
    return 'seq<string>',f'VHeaderFields({encoder.expr(node.args[0])})'


# CPython PSF-licensed dependency body. Keep the executable shape and local names
# for bytecode provenance. No globals, callbacks, defaults or mutable inputs.
def _reference_parse_http_list(s):
    res = []
    part = ''
    escape = quote = False
    for cur in s:
        if escape:
            part += cur
            escape = False
            continue
        if quote:
            if cur == '\\':
                escape = True
                continue
            elif cur == '"':
                quote = False
            part += cur
            continue
        if cur == ',':
            res.append(part)
            part = ''
            continue
        if cur == '"':
            quote = True
        part += cur
    if part:
        res.append(part)
    return [part.strip() for part in res]


def signature(fn):
    from types import FunctionType,CodeType
    if type(fn) is not FunctionType or fn.__defaults__ is not None or fn.__kwdefaults__ is not None or fn.__closure__ is not None:return None
    def code(c):
        # Nested comprehension bytecode is compared too. Only the outer docstring
        # differs between the reference and the standard-library declaration.
        return (c.co_code,tuple(code(v) if isinstance(v,CodeType) else v for v in c.co_consts),c.co_names,c.co_varnames,c.co_argcount,c.co_posonlyargcount,c.co_kwonlyargcount,c.co_flags,c.co_freevars,c.co_cellvars)
    c=fn.__code__;return code(c.replace(co_consts=(None,*c.co_consts[1:])))


def guard_dependency(function,names):
    from functools import wraps
    from types import FunctionType
    from veripy.guards.runtime import PreconditionError
    fingerprint=signature
    expected=fingerprint(_reference_parse_http_list)
    def checked(*args,**kwargs):
        for name in names:
            if fingerprint(function.__globals__.get(name))!=expected:
                raise PreconditionError(function.__name__,'HTTP list parser dependency changed: '+name)
        return function(*args,**kwargs)
    return wraps(function)(FunctionType(checked.__code__,function.__globals__,closure=checked.__closure__))


def guard_code(module,specs):
    names=imports(module)
    if not names:return ''
    return ('from veripy.backends.dafny.http_lists import guard_dependency as _veripy_guard_http_list\n'+
            ''.join(f'{sp.name} = _veripy_guard_http_list({sp.name}, {sorted(names)!r})\n' for sp in specs.functions))
