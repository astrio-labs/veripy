"""Runtime-identity NewType declarations and body-free exception subclasses."""
import ast
import copy


def resolve(module):
    imports={a.asname or a.name:a.name for n in module.body if isinstance(n,ast.ImportFrom) and n.module=='typing' and not n.level for a in n.names if a.name in {'NewType','cast'}}
    types={};exceptions={};remaining=[];available=set()
    stdnum_errors={'ValidationError':'ValueError','InvalidFormat':'ValidationError','InvalidChecksum':'ValidationError',
                   'InvalidLength':'InvalidFormat','InvalidComponent':'ValidationError'}
    for node in module.body:
        if isinstance(node,ast.ImportFrom) and node.module=='stdnum.exceptions' and not node.level:
            if any(a.asname or a.name not in {*stdnum_errors,'*'} for a in node.names):
                raise ValueError('stdnum exception imports require explicit unaliased modeled classes')
            selected=set(stdnum_errors) if any(a.name=='*' for a in node.names) else {a.name for a in node.names}
            # The original wildcard exports exactly this pinned hierarchy. An
            # explicit subset must include its parents so guards can check it.
            if any(stdnum_errors[name]!='ValueError' and stdnum_errors[name] not in selected for name in selected):
                raise ValueError('stdnum exception closure must include parent classes')
            exceptions.update((name,base) for name,base in stdnum_errors.items() if name in selected)
            continue
        if isinstance(node,ast.ImportFrom) and node.module=='typing' and not node.level:
            available.update(a.asname or a.name for a in node.names if a.name=='NewType')
        if (isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name)
                and isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Name)
                and node.value.func.id in available):
            call=node.value;name=node.targets[0].id
            if (call.keywords or len(call.args)!=2 or not isinstance(call.args[0],ast.Constant) or call.args[0].value!=name
                    or not isinstance(call.args[1],ast.Name) or call.args[1].id not in {'str','int','bool'}):
                raise ValueError('NewType declarations require a matching literal name and builtin scalar base')
            if name in types or name in exceptions:raise ValueError('NewType dependency is rebound')
            types[name]=call.args[1].id
        elif (isinstance(node,ast.ClassDef) and len(node.bases)==1 and isinstance(node.bases[0],ast.Name)
                and node.bases[0].id in {'ValueError',*exceptions}):
            if (node.decorator_list or node.keywords or getattr(node,'type_params',())
                    or any(not (isinstance(n,ast.Pass) or isinstance(n,ast.Expr) and isinstance(n.value,ast.Constant) and type(n.value.value) is str) for n in node.body)):
                raise ValueError('exception declarations require an unmodified builtin constructor')
            if node.name in types or node.name in exceptions:raise ValueError("exception declaration is rebound")
            exceptions[node.name]=node.bases[0].id
        else:remaining.append(node)
    names=set(types)|set(exceptions)
    if names:
        for node in remaining:
            if isinstance(node,(ast.FunctionDef,ast.ClassDef)):
                if node.name in names|set(imports):raise ValueError('definition replaces a modeled declaration')
                if isinstance(node,ast.FunctionDef):continue
            for n in ast.walk(node):
                if isinstance(n,ast.Name) and isinstance(n.ctx,(ast.Store,ast.Del)) and n.id in names|set(imports)|{'str','int','bool','ValueError'}:
                    raise ValueError('modeled declaration is rebound')
                if isinstance(n,ast.alias) and ((n.asname or n.name) in names or n.name=='*'):
                    raise ValueError('import can replace a modeled declaration')
        # Validate imported intrinsic provenance and order.
        for node in module.body:
            if isinstance(node,(ast.Import,ast.ImportFrom)):
                for a in node.names:
                    if (a.asname or a.name) in imports and not (isinstance(node,ast.ImportFrom) and node.module=='typing' and not node.level and a.name==imports[a.asname or a.name]):
                        raise ValueError('typing intrinsic is rebound')
    result=copy.deepcopy(ast.Module(body=remaining,type_ignores=module.type_ignores))
    class Annotation(ast.NodeTransformer):
        def visit_Name(self,node):
            if node.id in types:return ast.copy_location(ast.Name(id=types[node.id],ctx=node.ctx),node)
            return node
    for fn in result.body:
        if isinstance(fn,ast.FunctionDef):
            for a in (*fn.args.posonlyargs,*fn.args.args,*fn.args.kwonlyargs):
                if a.annotation is not None:a.annotation=Annotation().visit(a.annotation)
            if fn.returns is not None:fn.returns=Annotation().visit(fn.returns)
    return result,types,exceptions,{name for name,kind in imports.items() if kind=='cast'}


def guard_declarations(function,newtypes,exceptions,casts):
    from functools import wraps
    from types import FunctionType
    from typing import NewType, cast
    from veripy.guards.runtime import PreconditionError
    bases={'str':str,'int':int,'bool':bool}
    identity=NewType('_ModelIdentity',str).__call__
    original_types={name:function.__globals__.get(name) for name in {*newtypes,*exceptions}}
    def checked(*args,**kwargs):
        namespace=function.__globals__
        for name,base in newtypes.items():
            actual=namespace.get(name)
            if actual is not original_types[name] or type(actual) is not NewType or actual.__supertype__ is not bases[base] or actual.__call__ is not identity:
                raise PreconditionError(function.__name__,'NewType dependency changed: '+name)
        for name in casts:
            if namespace.get(name) is not cast:raise PreconditionError(function.__name__,'cast dependency changed: '+name)
        for name,parent in exceptions.items():
            actual=namespace.get(name);base=ValueError if parent=='ValueError' else namespace.get(parent)
            if actual is not original_types[name] or type(actual) is not type or actual.__bases__!=(base,) or actual.__init__ is not ValueError.__init__ or actual.__new__ is not ValueError.__new__:
                raise PreconditionError(function.__name__,'exception dependency changed: '+name)
        return function(*args,**kwargs)
    return wraps(function)(FunctionType(checked.__code__,function.__globals__,closure=checked.__closure__))


def guard_code(module,specs):
    _,newtypes,exceptions,casts=resolve(module)
    if not newtypes and not exceptions:return ''
    return ('from veripy.backends.dafny.declarations import guard_declarations as _veripy_guard_declarations\n'
            + ''.join(f'{sp.name} = _veripy_guard_declarations({sp.name}, {newtypes!r}, {exceptions!r}, {casts!r})\n' for sp in specs.functions))
