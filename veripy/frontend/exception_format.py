"""A bounded percent-format grammar for discarded exception-message text."""
import ast


def percent_char_operand(node):
    """Validate literal text with exactly one %c (and optional %% escapes).

    Only builtin strings are modeled by callers. They must evaluate the operand
    and check length == 1 before raising the requested exception. In particular,
    empty/multicharacter strings raise TypeError during Python formatting.
    """
    if not (isinstance(node,ast.BinOp) and isinstance(node.op,ast.Mod)
            and isinstance(node.left,ast.Constant) and type(node.left.value) is str):
        raise ValueError('exception percent formatting requires a literal format')
    text=node.left.value;index=0;count=0
    while index<len(text):
        if text[index]!='%':index+=1;continue
        index+=1
        if index==len(text) or text[index] not in ('%','c'):
            raise ValueError('exception percent formatting supports only %c and %%')
        count+=text[index]=='c';index+=1
    if count!=1:raise ValueError('exception percent formatting requires exactly one %c')
    if any(isinstance(n,ast.Call) for n in ast.walk(node.right)):
        raise ValueError('exception %c operand must be call-free')
    return node.right
