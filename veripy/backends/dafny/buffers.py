"""Explicit disjoint bytearray parameters modeled as mutable Dafny arrays.

The source signature and body are unchanged. A compiler-only fresh name handles
Python parameters named result; buffer("result") denotes that parameter's state.
"""
import ast
import copy
from ..base import register_backend
from .backend import DafnyBackend
from .encoder import _MethodEncoder, EncodeError, EncodedModule, _err, _module_shadow_check, _checked_defaults
from .preamble import PREAMBLE


class BufferEncoder(_MethodEncoder):
    def __init__(self,node,spec,*args,**kwargs):
        original=node
        if node.decorator_list or getattr(node,'type_params',()) or node.args.vararg or node.args.kwarg:
            raise _err(node,'buffer functions require a fixed undecorated signature')
        if not isinstance(node.returns,ast.Constant) or node.returns.value is not None:
            raise _err(node,'buffer functions return None and expose mutation through buffer(name)')
        self.buffers={p.arg:p.arg for p in (*node.args.posonlyargs,*node.args.args,*node.args.kwonlyargs)
                      if isinstance(p.annotation,ast.Name) and p.annotation.id=='bytearray'}
        if not self.buffers:raise _err(node,'buffer mode requires a bytearray parameter')
        policies=[]
        for clause in spec.by_kind('requires'):
            if not clause.desugared:continue
            expr=ast.parse(clause.desugared,mode='eval').body
            if not isinstance(expr,ast.Call) or not isinstance(expr.func,ast.Name) or expr.keywords:continue
            if expr.func.id=='disjoint_buffers' and not expr.args:policies.append(frozenset())
            elif expr.func.id=='allow_buffer_alias' and len(expr.args)==2:
                if not all(isinstance(a,ast.Constant) and a.value in self.buffers for a in expr.args):raise _err(node,'alias policy requires original buffer-name strings')
                pair=frozenset(a.value for a in expr.args)
                if len(pair)!=2:raise _err(node,'alias policy names two different parameters')
                policies.append(pair)
        if len(policies)!=1:raise _err(node,'buffer mode requires exactly one explicit disjoint_buffers() or allow_buffer_alias(a,b) policy')
        self.allowed_alias=policies[0]
        used={n.id for n in ast.walk(node) if isinstance(n,ast.Name)}|{p.arg for p in (*node.args.posonlyargs,*node.args.args,*node.args.kwonlyargs)}
        if 'result' in self.buffers:
            fresh='buffer_result'
            while fresh in used:fresh+='_' 
            self.buffers['result']=fresh
        node=copy.deepcopy(node)
        mapping=self.buffers
        class Rename(ast.NodeTransformer):
            def visit_Name(self,n):return ast.copy_location(ast.Name(id=mapping.get(n.id,n.id),ctx=n.ctx),n)
        node.body=[Rename().visit(n) for n in node.body]
        for p in (*node.args.posonlyargs,*node.args.args,*node.args.kwonlyargs):
            if p.arg in mapping:p.arg=mapping[p.arg]
            elif not isinstance(p.annotation,ast.Name) or p.annotation.id!='int':raise _err(p,'buffer mode permits int and bytearray parameters only')
        self.written={n.value.id for n in ast.walk(node) if isinstance(n,ast.Subscript) and isinstance(n.ctx,ast.Store) and isinstance(n.value,ast.Name)}
        if not self.written <= set(mapping.values()):raise _err(node,'buffer writes must target declared parameters directly')
        if any(isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef,ast.Lambda,ast.ClassDef,ast.Global,ast.Nonlocal,ast.Import,ast.ImportFrom)) for statement in node.body for n in ast.walk(statement)):
            raise _err(node,'buffer bodies must be closed scalar/array code')
        for clause in spec.clauses:
            if clause.desugared and any(isinstance(n,ast.Name) and n.id=='result' for n in ast.walk(ast.parse(clause.desugared,mode='eval'))):
                raise _err(original,'None buffer contracts use buffer("result"), not the result specification word')
        super().__init__(node,spec,*args,**kwargs)

    def _infer(self,node):
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name):
            if node.func.id in {'buffer','old_buffer'}:return 'seq<int>'
            if node.func.id in {'disjoint_buffers','allow_buffer_alias'}:return 'bool'
        if isinstance(node,ast.Subscript) and self._infer(node.value)=='array<int>':
            return 'seq<int>' if isinstance(node.slice,ast.Slice) else 'int'
        return super()._infer(node)

    def _call(self,node):
        if isinstance(node.func,ast.Name):
            name=node.func.id
            if name in {'disjoint_buffers','allow_buffer_alias'}:
                if not self.spec_mode or self._spec_clause_kind!='requires' or node.keywords:raise _err(node,'buffer alias policy is requires-only')
                if name=='disjoint_buffers':
                    if node.args:raise _err(node,'disjoint_buffers takes no arguments')
                    allowed=frozenset()
                else:
                    if len(node.args)!=2 or not all(isinstance(a,ast.Constant) and a.value in self.buffers for a in node.args):raise _err(node,'alias policy requires two buffer-name strings')
                    allowed=frozenset(a.value for a in node.args)
                names=list(self.buffers)
                pairs=[f'{self._mangle(self.buffers[a])} != {self._mangle(self.buffers[b])}' for i,a in enumerate(names) for b in names[i+1:] if frozenset({a,b})!=allowed]
                return '('+' && '.join(pairs)+')' if pairs else 'true'
            if name in {'buffer','old_buffer'}:
                if not self.spec_mode or node.keywords or len(node.args)!=1 or not isinstance(node.args[0],ast.Constant) or node.args[0].value not in self.buffers:
                    raise _err(node,'buffer accessors require one original parameter-name string in a specification')
                value=self._mangle(self.buffers[node.args[0].value])+'[..]'
                if name=='old_buffer':
                    if self._spec_clause_kind=='requires':raise _err(node,'old_buffer is a post-state or loop accessor')
                    value='old('+value+')'
                return value
            if name=='len' and len(node.args)==1 and not node.keywords and self._infer(node.args[0])=='array<int>':
                return self.expr(node.args[0])+'.Length'
        return super()._call(node)

    def expr(self,node):
        if isinstance(node,ast.Subscript) and self._infer(node.value)=='array<int>':
            value=super().expr(node.value)
            if isinstance(node.slice,ast.Slice):raise _err(node,'array slices use buffer(name) in specifications')
            return f'{value}[{self.expr(node.slice)}]' if self._known_nonnegative(node.slice) else f'{value}[PyIndex({self.expr(node.slice)}, {value}.Length)]'
        return super().expr(node)

    def stmt(self,stmt,indent):
        if isinstance(stmt,ast.Assign) and len(stmt.targets)>1:
            if not all(isinstance(t,ast.Name) for t in stmt.targets) or self._infer(stmt.value) not in {'int','bool'}:
                raise _err(stmt,'chained buffer assignments require scalar name targets')
            value=self._capture_scalar(stmt.value,indent)
            for target in stmt.targets:super().stmt(ast.copy_location(ast.Assign(targets=[target],value=value),stmt),indent)
            return
        if (isinstance(stmt,ast.Assign) and len(stmt.targets)==1 and isinstance(stmt.targets[0],ast.Subscript)
                and isinstance(stmt.targets[0].value,ast.Name) and stmt.targets[0].value.id in self.written):
            target=stmt.targets[0]
            if isinstance(target.slice,ast.Slice):raise _err(stmt,'buffer writes require an integer index')
            for clause in self._proofs_by_stmt.pop(id(stmt),[]):self._emit_proof(clause,indent)
            rhs=self._capture_scalar(stmt.value,indent,'int')
            index=self._capture_scalar(target.slice,indent,'int')
            name=self._mangle(target.value.id)
            self.emit(f'{indent}assert 0 <= {self.expr(rhs)} < 256;',stmt.lineno)
            self.emit(f'{indent}{name}[PyIndex({self.expr(index)}, {name}.Length)] := {self.expr(rhs)};',stmt.lineno)
            return
        if isinstance(stmt,ast.Return):
            if stmt.value is not None and not (isinstance(stmt.value,ast.Constant) and stmt.value.value is None):raise _err(stmt,'buffer methods return None')
            self.emit(indent+'return;',stmt.lineno);return
        return super().stmt(stmt,indent)

    def _ranges(self):
        binder = self._fresh('byte_index')
        return tuple(f'(forall {binder} :: 0 <= {binder} < {self._mangle(name)}.Length ==> 0 <= {self._mangle(name)}[{binder}] < 256)' for name in self.buffers.values())

    def _loop_clauses(self,loop,indent,extra=()):
        super()._loop_clauses(loop,indent,extra+self._ranges())

    def encode(self):
        node=self.node
        if node.args.defaults or any(d is not None for d in node.args.kw_defaults):raise _err(node,'buffer defaults are not modeled')
        for p in (*node.args.posonlyargs,*node.args.args,*node.args.kwonlyargs):
            self.types[p.arg]='array<int>' if p.arg in self.buffers.values() else 'int'
        self.return_type='bool'
        # Resolve scalar local types to a fixed point before branch hoisting.
        # This is type information only; Dafny still checks definite assignment.
        for _ in range(len(list(ast.walk(node)))):
            changed=False
            for assignment in ast.walk(node):
                if not isinstance(assignment,ast.Assign):continue
                dtype=self._infer(assignment.value)
                if dtype is None:continue
                for target in assignment.targets:
                    if isinstance(target,ast.Name) and target.id not in self.types:
                        self.types[target.id]=dtype;changed=True
            if not changed:break
        self.hoisted=self._hoist_analysis()
        params=', '.join(f'{self._mangle(p.arg)}: {self.types[p.arg]}' for p in (*node.args.posonlyargs,*node.args.args,*node.args.kwonlyargs))
        isolate = '{:isolate_assertions} ' if self.spec.by_kind('ghost_ensures') else ''
        self.emit(f'method {isolate}{self._mangle(node.name)}({params})',node.lineno)
        for requirement in self._ranges():self.emit('  requires '+requirement)
        for kind in ['requires','ensures','ghost_ensures']:
            for clause in self.spec.by_kind(kind):self.emit('  '+('ensures' if kind=='ghost_ensures' else kind)+' '+self.spec_expr(clause),clause.line)
        if self.written:self.emit('  modifies '+', '.join(self._mangle(n) for n in sorted(self.written)))
        self.emit('{')
        for name,dtype in self.hoisted.items():
            self.emit(f'  var {self._mangle(name)}: {dtype};');self.types.setdefault(name,dtype)
        self.block(node.body,'  ')
        self.emit('}')


def encode_buffers(source,specs,module_name='buffers.py',proof_lemmas=frozenset()):
    if specs.errors:raise EncodeError(str(specs.errors[0].error),specs.errors[0].line)
    module=ast.parse(source);_module_shadow_check(module)
    functions={(n.name,n.lineno):n for n in module.body if isinstance(n,ast.FunctionDef)}
    if len(functions)!=len(specs.functions) or any(not isinstance(n,ast.FunctionDef) for n in module.body):
        raise EncodeError('buffer modules contain only explicitly specified functions',None)
    lines=[*PREAMBLE.splitlines()];line_map={};names={}
    for spec in specs.functions:
        node=functions.get((spec.name,spec.lineno))
        if node is None:raise EncodeError('missing buffer function',spec.lineno)
        enc=BufferEncoder(node,spec,proof_lemmas,source_lines=source.splitlines())
        enc.encode();offset=len(lines);lines.extend(enc.lines)
        line_map.update({offset+i+1:line for i,line in enc.line_map.items()});names[spec.name]=enc._mangle(spec.name)
        for _,declaration,line in enc.quantified_functions.values():lines.extend(declaration)
    lines.append('// ---- STUB END: proof additions go below ----')
    return EncodedModule('\n'.join(lines)+'\n',line_map,list(names),names)


class BufferBackend(DafnyBackend):
    name='dafny-buffers'
    @property
    def preamble_version(self):return super().preamble_version+'-buffers-1-explicit-aliases'
    def encode(self,source,specs,*,module_name,proof_lemmas):return encode_buffers(source,specs,module_name,proof_lemmas)


register_backend('dafny-buffers',BufferBackend)
