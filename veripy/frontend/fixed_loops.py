"""Exact unrolling and first-iteration peeling of small literal range loops.

Only flat loops, no return/continue or loop-target rebinding. Break is preserved
by a fresh continuation flag. Annotated loops may peel first-iteration local initialization, retaining their
invariants on the remaining loop. No input bound or iteration is invented.
"""
import ast
import copy


def lower_fixed_loops(module, specs):
    module=copy.deepcopy(module)
    specifications={s.name:s for s in specs.functions}
    used={n.id for n in ast.walk(module) if isinstance(n,ast.Name)} | {n.arg for n in ast.walk(module) if isinstance(n,ast.arg)}
    class ReplaceTarget(ast.NodeTransformer):
        def __init__(self,name,value):self.name=name;self.value=value
        def visit_Name(self,n):
            return ast.copy_location(ast.Constant(self.value),n) if n.id==self.name and isinstance(n.ctx,ast.Load) else n
        def visit_If(self,n):
            self.generic_visit(n)
            t=n.test
            if isinstance(t,ast.Compare) and len(t.ops)==1 and isinstance(t.left,ast.Constant) and len(t.comparators)==1 and isinstance(t.comparators[0],ast.Constant):
                a,b=t.left.value,t.comparators[0].value
                if type(a) is int and type(b) is int and isinstance(t.ops[0],(ast.Eq,ast.NotEq,ast.Lt,ast.LtE,ast.Gt,ast.GtE)):
                    yes={ast.Eq:lambda:a==b,ast.NotEq:lambda:a!=b,ast.Lt:lambda:a<b,ast.LtE:lambda:a<=b,ast.Gt:lambda:a>b,ast.GtE:lambda:a>=b}[type(t.ops[0])]()
                    return n.body if yes else n.orelse
            return n
    for fn in module.body:
        if not isinstance(fn,ast.FunctionDef) or fn.name not in specifications:continue
        if any(c.kind=='proof' for c in specifications[fn.name].clauses):continue
        annotated=any(c.kind in ('invariant','decreases') for c in specifications[fn.name].clauses)
        result=[]
        for position,loop in enumerate(fn.body):
            if not (isinstance(loop,ast.For) and isinstance(loop.target,ast.Name) and not loop.orelse
                    and isinstance(loop.iter,ast.Call) and isinstance(loop.iter.func,ast.Name) and loop.iter.func.id=='range'
                    and not loop.iter.keywords and len(loop.iter.args) in (1,2)
                    and all(isinstance(a,ast.Constant) and type(a.value) is int for a in loop.iter.args)):
                result.append(loop);continue
            bounds=[a.value for a in loop.iter.args];start,stop=(0,bounds[0]) if len(bounds)==1 else bounds
            if not (0<=start<stop and stop-start<=8):result.append(loop);continue
            nodes=[n for stmt in loop.body for n in ast.walk(stmt)]
            if any(isinstance(n,(ast.For,ast.While,ast.AsyncFor,ast.Try,ast.Return,ast.Continue,ast.FunctionDef,ast.ClassDef,ast.Lambda,ast.ListComp,ast.GeneratorExp,ast.DictComp,ast.SetComp)) for n in nodes) or any(isinstance(n,ast.Name) and n.id==loop.target.id and isinstance(n.ctx,(ast.Store,ast.Del)) for n in nodes):
                result.append(loop);continue
            if annotated:
                before={n.id for stmt in fn.body[:position] for n in ast.walk(stmt) if isinstance(n,ast.Name) and isinstance(n.ctx,ast.Store)} | {a.arg for a in (*fn.args.posonlyargs,*fn.args.args,*fn.args.kwonlyargs)}
                first_init=any(isinstance(stmt,ast.If) and not stmt.orelse
                    and isinstance(stmt.test,ast.Compare) and isinstance(stmt.test.left,ast.Name)
                    and stmt.test.left.id==loop.target.id and len(stmt.test.ops)==1
                    and isinstance(stmt.test.ops[0],ast.Eq) and len(stmt.test.comparators)==1
                    and isinstance(stmt.test.comparators[0],ast.Constant)
                    and type(stmt.test.comparators[0].value) is int and stmt.test.comparators[0].value==start
                    and any(isinstance(n,ast.Name) and isinstance(n.ctx,ast.Store) and n.id not in before for child in stmt.body for n in ast.walk(child))
                    for stmt in loop.body)
                escapes=loop.target.id in before or any(isinstance(n,ast.Name) and n.id==loop.target.id and isinstance(n.ctx,ast.Load) for stmt in fn.body[position+1:] for n in ast.walk(stmt))
                if not first_init or stop-start<2 or escapes:
                    result.append(loop);continue
            flag='__vp_fixed_active_'+str(loop.lineno)
            while flag in used:flag+='_'
            used.add(flag)
            def flag_expr():return ast.Name(id=flag,ctx=ast.Load())
            def protect(body):
                output=[]
                for index,statement in enumerate(body):
                    may_break=any(isinstance(n,ast.Break) for n in ast.walk(statement))
                    if isinstance(statement,ast.Break):
                        statement=ast.copy_location(ast.Assign(targets=[ast.Name(id=flag,ctx=ast.Store())],value=ast.Constant(False)),statement)
                    elif isinstance(statement,ast.If):
                        statement.body=protect(statement.body);statement.orelse=protect(statement.orelse)
                    output.append(statement)
                    if may_break and index+1<len(body):
                        output.append(ast.copy_location(ast.If(test=flag_expr(),body=protect(body[index+1:]),orelse=[]),body[index+1]))
                        break
                return output
            result.append(ast.copy_location(ast.Assign(targets=[ast.Name(id=flag,ctx=ast.Store())],value=ast.Constant(True)),loop))
            if annotated:
                first=ReplaceTarget(loop.target.id,start).visit(ast.Module(body=copy.deepcopy(loop.body),type_ignores=[])).body
                result.extend(protect(first))
                rest=copy.deepcopy(loop)
                rest._veripy_peeled=True
                rest.iter.args=[ast.copy_location(ast.Constant(start+1),loop.iter),ast.copy_location(ast.Constant(stop),loop.iter)]
                result.append(ast.copy_location(ast.If(test=flag_expr(),body=[rest],orelse=[]),loop))
                continue
            iterations=[]
            for value in reversed(range(start,stop)):
                body=[ast.copy_location(ast.Assign(targets=[copy.deepcopy(loop.target)],value=ast.Constant(value)),loop)]
                transformed=ReplaceTarget(loop.target.id,value).visit(ast.Module(body=copy.deepcopy(loop.body),type_ignores=[])).body
                body+=protect(transformed)
                if iterations:
                    body.append(ast.copy_location(ast.If(test=flag_expr(),body=iterations,orelse=[]),loop))
                iterations=body
            result.extend(iterations)
        fn.body=result
    return ast.fix_missing_locations(module)
