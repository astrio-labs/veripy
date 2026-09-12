"""Explicit import inventory for the closed verification environment.

An inventory entry is not a contract. Only the encoder for the named operation
can admit its use. Third-party imports stay unresolved until a checked model or
body closure is supplied; importing a package never imports proof authority.
"""
import ast

_MODELS = {
    ('__future__', 'annotations'): 'annotation syntax',
    ('typing','NewType'): 'validated scalar identity declaration',
    ('typing','cast'): 'validated scalar NewType cast',
    ('werkzeug','datastructures'): 'ETags constructor model only when its pinned regex dependency is declared',
    ('typing', 'Optional'): 'optional type',
    ('typing', 'Tuple'): 'tuple type',
    ('typing', 'List'): 'sequence type',
    ('dataclasses', 'dataclass'): 'validated frozen record declaration',
    ('math', 'gcd'): 'PyGcd',
    ('math', 'factorial'): 'PyFact',
    ('math', 'isqrt'): 'PyIsqrt',
    ('math', 'prod'): 'PyProd',
    ('bisect', 'bisect_right'): 'PyBisectRight',
    ('bisect', 'insort'): 'owned sequence insertion',
}
for _exception in ['*','ValidationError','InvalidFormat','InvalidChecksum','InvalidLength','InvalidComponent']:
    _MODELS[('stdnum.exceptions',_exception)]='validated ValueError subclass hierarchy'

_MODULES = {'re':'exact registered pattern declarations and operations only','math': 'operation-specific arithmetic models',
            'typing': 'annotation syntax only',
            'sys': 'supported sys configuration constants only'}


def inventory(module: ast.Module) -> list[dict]:
    rows = []
    for node in module.body:
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        for item in node.names:
            imported_module = node.module if isinstance(node, ast.ImportFrom) else item.name
            symbol = item.name if isinstance(node, ast.ImportFrom) else None
            relative = node.level if isinstance(node, ast.ImportFrom) else 0
            model = None if relative else (_MODELS.get((imported_module,symbol)) if symbol is not None else _MODULES.get(imported_module))
            rows.append({'module':imported_module,'symbol':symbol,
                         'binding':item.asname or item.name.split('.')[0],
                         'relative_level':relative,'line':node.lineno,
                         'resolution':'encoder-model' if model else 'unresolved',
                         'model':model,'executed_by_resolver':False})
    return rows
