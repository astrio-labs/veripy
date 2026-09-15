"""Bytearray guards retain mutation and enforce the explicit alias policy."""
import ast
import functools
import hashlib
import inspect
from veripy.guards.runtime import PreconditionError,PostconditionError,guard_value


def _make_buffer_guard(function,buffer_names,requires,ensures,allowed_alias=()):
    signature=inspect.signature(function)
    @functools.wraps(function)
    def guarded(*args,**kwargs):
        bound=signature.bind(*args,**kwargs);bound.apply_defaults()
        for name,value in bound.arguments.items():
            if name in buffer_names:
                if type(value) is not bytearray:raise PreconditionError(function.__name__,'buffer parameters require exact bytearray objects')
            else:guard_value(value,('int',),function=function.__name__,param=name)
        buffers={name:bound.arguments[name] for name in buffer_names}
        names=list(buffers)
        for i,a in enumerate(names):
            for b in names[i+1:]:
                if buffers[a] is buffers[b] and set((a,b))!=set(allowed_alias):
                    raise PreconditionError(function.__name__,'buffer alias policy failed')
        old={name:bytes(value) for name,value in buffers.items()}
        env=dict(function.__globals__);env.update(bound.arguments)
        env.update(buffer=lambda name:buffers[name],old_buffer=lambda name:old[name],disjoint_buffers=lambda:len({id(v) for v in buffers.values()})==len(buffers),
                   allow_buffer_alias=lambda a,b:set((a,b))==set(allowed_alias))
        for requirement in requires:
            try:ok=bool(eval(requirement,env))
            except Exception as exc:raise PreconditionError(function.__name__,'buffer requires evaluation failed') from exc
            if not ok:raise PreconditionError(function.__name__,'buffer requires failed')
        returned=function(*bound.args,**bound.kwargs)
        if returned is not None:raise PostconditionError(function.__name__,'buffer function must return None')
        for post in ensures:
            try:ok=bool(eval(post,env))
            except Exception as exc:raise PostconditionError(function.__name__,'buffer ensures evaluation failed') from exc
            if not ok:raise PostconditionError(function.__name__,'buffer ensures failed')
        return None
    return guarded


def emit_buffer_guarded(source,specs,src_name,*,check_ensures=False,proof_lemmas=frozenset()):
    from veripy.backends.dafny.buffers import encode_buffers
    from veripy.guards.emitter import _reject_reserved_names
    encode_buffers(source,specs,src_name,proof_lemmas)
    module=ast.parse(source);_reject_reserved_names(module)
    functions={(n.name,n.lineno):n for n in module.body if isinstance(n,ast.FunctionDef)}
    wrappers=[]
    for spec in specs.functions:
        fn=functions[(spec.name,spec.lineno)]
        buffers=tuple(a.arg for a in (*fn.args.posonlyargs,*fn.args.args,*fn.args.kwonlyargs) if isinstance(a.annotation,ast.Name) and a.annotation.id=='bytearray')
        requires=tuple(c.desugared for c in spec.by_kind('requires'))
        ensures=tuple(c.desugared for c in spec.by_kind('ensures')) if check_ensures else ()
        allowed=()
        for requirement in requires:
            expr=ast.parse(requirement,mode='eval').body
            if isinstance(expr,ast.Call) and isinstance(expr.func,ast.Name) and expr.func.id=='allow_buffer_alias':
                allowed=tuple(a.value for a in expr.args)
        wrappers.append(f'{fn.name} = _veripy_buffer_guard({fn.name}, {buffers!r}, {requires!r}, {ensures!r}, {allowed!r})\n')
    digest=hashlib.sha256(source.rstrip('\n').encode()).hexdigest()
    return ('from veripy.guards.buffers import _make_buffer_guard as _veripy_buffer_guard\n'
            '# ---- VERIPY ISLAND BEGIN (verbatim copy of the admitted source) ----\n'+source.rstrip('\n')+
            '\n# ---- VERIPY ISLAND END ----\n'+f'_VERIPY_ISLAND_SHA256 = {digest!r}\n'+''.join(wrappers))
