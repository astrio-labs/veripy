"""Closed, deterministic module initialization without executing user Python.

Only builtin scalar/container values and a bounded AST interpreter are admitted.
The bounds limit admission work, not the inputs of verified functions. Imported
Python functions are never called or granted contracts by this interpreter.
"""
from __future__ import annotations
import ast
import copy
from dataclasses import dataclass, field
import operator


class EnvironmentError(ValueError):
    def __init__(self,message,node):
        super().__init__(message);self.message=message;self.line=getattr(node,'lineno',None)


@dataclass
class ModuleEnvironment:
    module: ast.Module
    values: dict
    dependencies: list[dict]
    regex_models: dict = field(default_factory=dict)
    newtypes: dict = field(default_factory=dict)
    exceptions: dict = field(default_factory=dict)
    casts: set = field(default_factory=set)


def _safe_annotation(annotation):
    for node in ast.walk(annotation):
        if isinstance(node,(ast.Call,ast.NamedExpr,ast.Lambda)):
            return False
        if isinstance(node,ast.Subscript) and not (isinstance(node.value,ast.Name) and node.value.id in {'list','tuple','Optional','Tuple','List'}):
            return False
        if isinstance(node,ast.Attribute):
            return False
    return True


class _Returned(Exception):
    def __init__(self,value):self.value=value


class _Interpreter:
    def __init__(self):
        self.values={};self.functions={};self.remaining=10000;self.active=set();self.external=set()

    def tick(self,node):
        self.remaining-=1
        if self.remaining<0:raise EnvironmentError('module initialization exceeds the static evaluation budget',node)

    def bounded(self,value,node):
        if type(value) is int and value.bit_length()>16384:
            raise EnvironmentError('module integer exceeds static evaluation budget',node)
        if type(value) in (str,list,tuple) and len(value)>4096:
            raise EnvironmentError('module value exceeds static evaluation budget',node)
        if type(value) not in (int,bool,str,list,tuple):
            raise EnvironmentError('module constants require builtin int/bool/str/list/tuple values',node)
        return value

    def expr(self,n,scope):
        self.tick(n)
        if isinstance(n,ast.Constant):return self.bounded(n.value,n)
        if isinstance(n,ast.Name):
            if n.id not in scope:raise EnvironmentError(f'unresolved module dependency {n.id!r}',n)
            return scope[n.id]
        if isinstance(n,(ast.List,ast.Tuple)):
            values=[self.expr(x,scope) for x in n.elts]
            return self.bounded(values if isinstance(n,ast.List) else tuple(values),n)
        if isinstance(n,ast.UnaryOp):
            f={ast.USub:operator.neg,ast.UAdd:operator.pos,ast.Not:operator.not_,ast.Invert:operator.invert}.get(type(n.op))
            if f:return self.bounded(f(self.expr(n.operand,scope)),n)
        if isinstance(n,ast.BinOp):
            a,b=self.expr(n.left,scope),self.expr(n.right,scope)
            if isinstance(n.op,(ast.Pow,ast.LShift,ast.RShift)) and (type(b) is not int or not 0<=b<=4096):
                raise EnvironmentError('module exponent/shift exceeds static evaluation budget',n)
            if isinstance(n.op,ast.Mult) and ((type(a) in (str,list,tuple) and type(b) is int and len(a)*max(b,0)>4096) or (type(b) in (str,list,tuple) and type(a) is int and len(b)*max(a,0)>4096)):
                raise EnvironmentError('module repetition exceeds static evaluation budget',n)
            f={ast.Add:operator.add,ast.Sub:operator.sub,ast.Mult:operator.mul,ast.FloorDiv:operator.floordiv,ast.Mod:operator.mod,ast.Pow:operator.pow,ast.LShift:operator.lshift,ast.RShift:operator.rshift,ast.BitAnd:operator.and_,ast.BitOr:operator.or_,ast.BitXor:operator.xor}.get(type(n.op))
            if f:return self.bounded(f(a,b),n)
        if isinstance(n,ast.BoolOp):
            for node in n.values:
                value=self.expr(node,scope)
                if isinstance(n.op,ast.And) and not value or isinstance(n.op,ast.Or) and value:return value
            return value
        if isinstance(n,ast.Compare):
            a=self.expr(n.left,scope)
            for op,bnode in zip(n.ops,n.comparators):
                b=self.expr(bnode,scope)
                f={ast.Eq:operator.eq,ast.NotEq:operator.ne,ast.Lt:operator.lt,ast.LtE:operator.le,ast.Gt:operator.gt,ast.GtE:operator.ge}.get(type(op))
                if f is None:raise EnvironmentError('unsupported comparison in module initialization',n)
                if not f(a,b):return False
                a=b
            return True
        if isinstance(n,ast.IfExp):return self.expr(n.body if self.expr(n.test,scope) else n.orelse,scope)
        if isinstance(n,ast.Subscript):
            value=self.expr(n.value,scope)
            if isinstance(n.slice,ast.Slice):
                sl=n.slice;index=slice(*(self.expr(x,scope) if x is not None else None for x in (sl.lower,sl.upper,sl.step)))
            else:index=self.expr(n.slice,scope)
            return value[index]
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and not n.keywords:
            args=[self.expr(x,scope) for x in n.args];name=n.func.id
            if name in scope:raise EnvironmentError('initializer call is shadowed by a data binding',n)
            if name in {'len','divmod','range'}:
                if name=='range':
                    value=range(*args)
                    if len(value)>4096:raise EnvironmentError('module range exceeds static evaluation budget',n)
                    return list(value)
                return self.bounded({'len':len,'divmod':divmod}[name](*args),n)
            if name in self.functions:
                fn=self.functions[name];a=fn.args
                if name in self.active:raise EnvironmentError('recursive module initialization is unsupported',n)
                if fn.decorator_list or a.vararg or a.kwarg or a.defaults or a.kwonlyargs or len(args)!=len(a.posonlyargs)+len(a.args):
                    raise EnvironmentError('unsupported initializer helper signature',n)
                local=dict(self.values)
                for binding in ast.walk(fn):
                    if isinstance(binding,ast.Name) and isinstance(binding.ctx,(ast.Store,ast.Del)):
                        local.pop(binding.id,None)
                local.update(zip([p.arg for p in (*a.posonlyargs,*a.args)],args))
                self.active.add(name)
                try:
                    self.block(fn.body,local)
                except _Returned as ret:return self.bounded(ret.value,n)
                finally:self.active.remove(name)
                raise EnvironmentError('initializer helper requires an explicit value return',n)
        raise EnvironmentError('unsupported or unresolved dependency in module initializer: '+ast.unparse(n),n)

    def bind(self,target,value,scope):
        if isinstance(target,ast.Name):
            if target.id in self.functions or target.id in self.external or target.id in {'len','divmod','range'}:
                raise EnvironmentError('module initialization cannot replace a function or intrinsic',target)
            scope[target.id]=value;return
        if isinstance(target,(ast.Tuple,ast.List)) and type(value) in (tuple,list) and len(target.elts)==len(value):
            for t,v in zip(target.elts,value):self.bind(t,v,scope)
            return
        raise EnvironmentError('unsupported module assignment target',target)

    def block(self,body,scope):
        for n in body:
            self.tick(n)
            if isinstance(n,ast.Assign):
                if any(isinstance(t,ast.Name) and t.id in self.functions for target in n.targets for t in ast.walk(target)):
                    raise EnvironmentError('module initialization/rebinding cannot replace a function',n)
                value=self.expr(n.value,scope)
                for target in n.targets:self.bind(target,value,scope)
            elif isinstance(n,ast.AnnAssign) and n.value is not None:
                if not _safe_annotation(n.annotation):
                    raise EnvironmentError('module annotations cannot execute calls',n)
                self.bind(n.target,self.expr(n.value,scope),scope)
            elif isinstance(n,ast.AugAssign):
                if isinstance(n.op,(ast.Add,ast.Mult)) and isinstance(n.target,ast.Name) and type(scope.get(n.target.id)) is list:
                    receiver=scope[n.target.id];value=self.expr(n.value,scope)
                    if isinstance(n.op,ast.Mult):
                        if type(value) not in (int,bool):raise EnvironmentError('initializer list multiplier must be an integer',n)
                        if len(receiver)*max(value,0)>4096:raise EnvironmentError('module value exceeds static evaluation budget',n)
                        receiver *= value
                    else:
                        if type(value) not in (list,tuple,str):raise EnvironmentError('unsupported initializer in-place addition',n)
                        if len(receiver)+len(value)>4096:raise EnvironmentError('module value exceeds static evaluation budget',n)
                        receiver.extend(value)
                else:
                    self.bind(n.target,self.expr(ast.copy_location(ast.BinOp(left=n.target,op=n.op,right=n.value),n),scope),scope)
            elif isinstance(n,ast.For) and not n.orelse:
                values=self.expr(n.iter,scope)
                if type(values) not in (list,tuple,str):raise EnvironmentError('module iteration requires a finite builtin sequence',n)
                for value in values:self.bind(n.target,value,scope);self.block(n.body,scope)
            elif isinstance(n,ast.If):self.block(n.body if self.expr(n.test,scope) else n.orelse,scope)
            elif isinstance(n,ast.Assert):
                if not self.expr(n.test,scope):raise EnvironmentError('module initialization assertion fails',n)
            elif isinstance(n,ast.Delete):
                for target in n.targets:
                    if not isinstance(target,ast.Name) or target.id not in scope:raise EnvironmentError('unsupported module deletion',n)
                    del scope[target.id]
            elif isinstance(n,ast.Return):raise _Returned(self.expr(n.value,scope))
            elif isinstance(n,ast.Expr) and isinstance(n.value,ast.Constant) and isinstance(n.value.value,str):pass
            elif isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='append' and len(n.value.args)==1 and not n.value.keywords:
                receiver=self.expr(n.value.func.value,scope)
                if type(receiver) is not list:raise EnvironmentError('initializer append requires a builtin list',n)
                receiver.append(self.expr(n.value.args[0],scope));self.bounded(receiver,n)
            else:raise EnvironmentError('unsupported module initialization statement',n)


def resolve_module(module: ast.Module) -> ModuleEnvironment:
    """Resolve finite initializers; retain functions/imports/records for admission.

    Values describe the stable module environment required by the proof.
    External rebinding/mutation is outside it; generated guards check it.
    """
    from veripy.backends.dafny.dependencies import inventory
    from veripy.backends.dafny.regex_strings import declarations
    dependencies=inventory(module)
    try:
        module,regex_models=declarations(module)
        from veripy.backends.dafny.declarations import resolve
        module,newtypes,exceptions,casts=resolve(module)
    except ValueError as exc:
        raise EnvironmentError(str(exc),module) from exc
    # A subscription in an eager annotation may execute __class_getitem__.
    # Only unshadowed builtin/typing generic constructors are safe here.
    generic_imports={}
    for n in module.body:
        if isinstance(n,(ast.Import,ast.ImportFrom)):
            for a in n.names:
                generic_imports[a.asname or a.name.split('.')[0]]=(n.module if isinstance(n,ast.ImportFrom) else a.name,a.name,getattr(n,'level',0))
    for n in ast.walk(module):
        if isinstance(n,ast.Subscript) and isinstance(n.value,ast.Name) and n.value.id in {'Optional','Tuple','List'}:
            expected=('typing',n.value.id,0)
            if generic_imports.get(n.value.id)!=expected:
                raise EnvironmentError('generic annotations require an explicit typing import',n)
    machine=_Interpreter();machine.external.update(set(regex_models)|set(newtypes)|set(exceptions));remaining=[]
    has_initializers=any(isinstance(n,(ast.Assign,ast.AnnAssign,ast.AugAssign,ast.For,ast.If,ast.Delete,ast.Assert)) for n in module.body)
    if not has_initializers:return ModuleEnvironment(module,{},dependencies,regex_models,newtypes,exceptions,casts)
    try:
        for n in module.body:
            if isinstance(n,ast.FunctionDef):
                annotations=[p.annotation for p in (*n.args.posonlyargs,*n.args.args,*n.args.kwonlyargs) if p.annotation is not None]
                if n.returns is not None:annotations.append(n.returns)
                if n.decorator_list or any(not _safe_annotation(annotation) for annotation in annotations):
                    raise EnvironmentError('definition-time calls/decorators cannot initialize module constants',n)
                if any(not isinstance(d,ast.Constant) or type(d.value) not in (int,bool,str,type(None)) for d in [*n.args.defaults,*[d for d in n.args.kw_defaults if d is not None]]):
                    raise EnvironmentError('definition-time defaults require immutable scalar literals',n)
                if n.name in machine.values or n.name in machine.external or n.name in machine.functions or n.name in {'len','divmod','range'}:raise EnvironmentError('module function replaces an existing binding or intrinsic',n)
                machine.functions[n.name]=n;remaining.append(n)
            elif isinstance(n,(ast.Import,ast.ImportFrom)):
                for a in n.names:
                    bound=a.asname or a.name.split('.')[0]
                    if bound in machine.values or bound in machine.functions or bound in {'len','divmod','range'}:raise EnvironmentError('import replaces a module value or intrinsic',n)
                    machine.external.add(bound)
                remaining.append(n)
            elif isinstance(n,ast.ClassDef):
                from veripy.frontend.records import record_schemas, RecordError
                try:
                    records=record_schemas(module)
                except RecordError as exc:
                    raise EnvironmentError(str(exc),n) from exc
                if n.name not in records:raise EnvironmentError('module class initialization requires an explicit declaration model',n)
                if n.name in machine.values or n.name in machine.functions or n.name in machine.external:
                    raise EnvironmentError('module class replaces an existing binding',n)
                machine.external.add(n.name);remaining.append(n)
            elif isinstance(n,ast.Expr) and isinstance(n.value,ast.Constant) and isinstance(n.value.value,str):remaining.append(n)
            else:machine.block([n],machine.values)
    except (TypeError,IndexError,KeyError,ZeroDivisionError,OverflowError) as exc:
        raise EnvironmentError('module initialization fails: '+str(exc),n) from exc
    # Executable globals/nonlocals would invalidate the resolved environment.
    for fn in machine.functions.values():
        if any(isinstance(n,(ast.Global,ast.Nonlocal)) for n in ast.walk(fn)):
            raise EnvironmentError('verified functions cannot rebind module constants',fn)
    def validate(value,active,depth):
        machine.tick(module)
        if depth>16:raise EnvironmentError('module value nesting exceeds static evaluation budget',module)
        machine.bounded(value,module)
        if type(value) in (list,tuple):
            if id(value) in active:raise EnvironmentError('cyclic module data is unsupported',module)
            for item in value:validate(item,active|{id(value)},depth+1)
    for value in machine.values.values():validate(value,set(),0)
    return ModuleEnvironment(ast.Module(body=remaining,type_ignores=module.type_ignores),copy.deepcopy(machine.values),dependencies,regex_models,newtypes,exceptions,casts)


def literal(value,node):
    """Build a data expression at the use site, without executing Python."""
    if type(value) is list:result=ast.List(elts=[literal(v,node) for v in value],ctx=ast.Load())
    elif type(value) is tuple:result=ast.Tuple(elts=[literal(v,node) for v in value],ctx=ast.Load())
    else:result=ast.Constant(value=value)
    return ast.copy_location(result,node)


def same_value(actual,expected):
    """Compare only exact builtin data; do not invoke user equality hooks."""
    if type(actual) is not type(expected):return False
    if type(expected) in (list,tuple):
        return len(actual)==len(expected) and all(same_value(a,b) for a,b in zip(actual,expected))
    return actual==expected


def guard_environment(function,expected):
    """Check stable module data at every guarded entry, including helper calls."""
    from functools import wraps
    from veripy.guards.runtime import PreconditionError
    from types import FunctionType
    same = same_value
    def checked(*args,**kwargs):
        for name,value in expected.items():
            if name not in function.__globals__ or not same(function.__globals__[name],value):
                raise PreconditionError(function.__name__,f'module environment changed: {name}')
        return function(*args,**kwargs)
    return wraps(function)(FunctionType(checked.__code__,function.__globals__,closure=checked.__closure__))


def resolve_for_encoder(module):
    """Keep the pre-existing math alias analysis responsible for its surface.

    That analysis tracks import snapshots, alias copies, deletion and mutation.
    It does not need to execute initialization or introduce data constants.
    Never use this path for initializer calls or a new third-party dependency.
    """
    try:
        return resolve_module(module)
    except EnvironmentError:
        initialization=[n for n in module.body if not isinstance(n,(ast.FunctionDef,ast.ClassDef))]
        nodes=[n for statement in initialization for n in ast.walk(statement)]
        imports=[n for n in nodes if isinstance(n,(ast.Import,ast.ImportFrom))]
        math_present=any(isinstance(n,ast.Import) and any(a.name=='math' for a in n.names) or isinstance(n,ast.ImportFrom) and n.module=='math' and not n.level for n in imports)
        if (math_present and not any(isinstance(n,ast.Call) for n in nodes)
                and all((isinstance(n,ast.Import) and all(a.name in {'math','typing'} for a in n.names))
                        or (isinstance(n,ast.ImportFrom) and n.module in {'math','typing','__future__'} and not n.level) for n in imports)):
            from veripy.backends.dafny.dependencies import inventory
            return ModuleEnvironment(module,{},inventory(module))
        raise
