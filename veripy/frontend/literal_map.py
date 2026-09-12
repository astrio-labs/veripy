"""Checked specialization of all/any(map(total literal-membership helper, str)).

Uses the actual helper body, never its postcondition. No effectful, partial,
stateful or arbitrary higher-order function is substituted.
"""
import ast
import copy


def expand_literal_map(node, functions):
    if not (isinstance(node,ast.Call) and isinstance(node.func,ast.Name)
            and node.func.id in ('all','any') and len(node.args)==1
            and isinstance(node.args[0],ast.Call) and isinstance(node.args[0].func,ast.Name)
            and node.args[0].func.id=='map'):
        return None
    call=node.args[0]
    if node.keywords or call.keywords or len(call.args)!=2 or not isinstance(call.args[0],ast.Name):
        raise ValueError('literal predicate map requires one helper and one iterable')
    fn=functions.get(call.args[0].id)
    if fn is None:raise ValueError('literal predicate map requires a specified local helper')
    args=fn.args;body=[n for n in fn.body if not (isinstance(n,ast.Expr) and isinstance(n.value,ast.Constant) and isinstance(n.value.value,str))]
    params=[*args.posonlyargs,*args.args]
    if fn.decorator_list or len(params)!=1 or args.defaults or args.kwonlyargs or args.vararg or args.kwarg or len(body)!=1 or not isinstance(body[0],ast.Return):
        raise ValueError('mapped helper must be a single-return total literal-membership predicate')
    value=body[0].value
    if not (isinstance(params[0].annotation,ast.Name) and params[0].annotation.id=='str'
            and isinstance(fn.returns,ast.Name) and fn.returns.id=='bool'
            and isinstance(value,ast.Compare) and len(value.ops)==1 and isinstance(value.ops[0],(ast.In,ast.NotIn))
            and isinstance(value.left,ast.Name) and value.left.id==params[0].arg
            and len(value.comparators)==1 and isinstance(value.comparators[0],ast.Constant)
            and type(value.comparators[0].value) is str):
        raise ValueError('mapped helper must return its string argument in/not-in a literal string')
    target=ast.Name(id=params[0].arg,ctx=ast.Store())
    gen=ast.GeneratorExp(elt=copy.deepcopy(value),generators=[ast.comprehension(target=target,iter=copy.deepcopy(call.args[1]),ifs=[],is_async=0)])
    result=ast.copy_location(ast.Call(func=copy.deepcopy(node.func),args=[gen],keywords=[]),node)
    return ast.fix_missing_locations(result)
