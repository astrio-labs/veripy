"""Closed frozen record schemas shared by lowering and boundaries.

Records have generated dataclass behavior only. No descriptors, inheritance,
defaults, methods, recursive schemas or class rebinding. Scalar list fields
are admitted only in read-only modules and are copied at the guard boundary.
"""
import ast
import re


class RecordError(ValueError):
    def __init__(self, message, line=None):
        super().__init__(message)
        self.line = line


def record_schemas(module: ast.Module) -> dict[str, tuple[tuple[str, ast.expr], ...]]:
    classes = [n for n in module.body if isinstance(n, ast.ClassDef)]
    candidates = [n for n in classes if any(
        isinstance(d, ast.Call) and isinstance(d.func, ast.Name) and d.func.id == "dataclass"
        for d in n.decorator_list)]
    if not candidates:
        return {}
    if not any(isinstance(n, ast.ImportFrom) and n.level == 0 and n.module == "dataclasses"
               and any(a.name == "dataclass" and a.asname is None for a in n.names)
               for n in module.body):
        raise RecordError("record schemas require `from dataclasses import dataclass`")
    schemas = {}
    for node in candidates:
        if not re.fullmatch(r"_?[A-Za-z][A-Za-z0-9_]*", node.name) or node.name in schemas:
            raise RecordError("record names must be unique ASCII identifiers", node.lineno)
        if node.bases or node.keywords or len(node.decorator_list) != 1:
            raise RecordError("record inheritance and extra decorators are outside the fragment", node.lineno)
        d = node.decorator_list[0]
        if d.args or len(d.keywords) != 1 or d.keywords[0].arg != "frozen" or not (
                isinstance(d.keywords[0].value, ast.Constant) and d.keywords[0].value.value is True):
            raise RecordError("records require exactly @dataclass(frozen=True)", node.lineno)
        fields = []
        for item in node.body:
            if isinstance(item, ast.Expr) and isinstance(item.value, ast.Constant) and isinstance(item.value.value, str):
                continue
            if not isinstance(item, ast.AnnAssign) or not isinstance(item.target, ast.Name) or item.value is not None:
                raise RecordError("records contain annotated fields only; no methods/defaults/descriptors", item.lineno)
            name = item.target.id
            if not re.fullmatch(r"[a-zA-Z][a-zA-Z0-9_]*", name) or name in {f for f, _ in fields}:
                raise RecordError("record fields must be unique plain identifiers", item.lineno)
            ann = item.annotation
            if not ((isinstance(ann, ast.Name) and ann.id in {"int", "bool", "str", *schemas}) or
                    (isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name)
                     and ann.value.id == "list" and isinstance(ann.slice, ast.Name)
                     and ann.slice.id in {"int", "bool", "str"})):
                raise RecordError("record fields must be scalars, scalar lists, or earlier frozen records", item.lineno)
            fields.append((name, ann))
        if not fields:
            raise RecordError("empty records are outside the fragment", node.lineno)
        schemas[node.name] = tuple(fields)
    # No initialization code may replace a schema/dataclass binding or install
    # user descriptors. Function bodies are separately checked by the encoder.
    names = {*schemas, "dataclass"}
    for node in module.body:
        if isinstance(node, ast.ClassDef):
            if node not in candidates:
                raise RecordError("only frozen record classes are admitted in record modules", node.lineno)
        elif isinstance(node, ast.FunctionDef):
            if node.name in names or node.decorator_list or node.args.defaults or any(x is not None for x in node.args.kw_defaults):
                raise RecordError("record modules cannot rebind schemas or execute decorators/defaults", node.lineno)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module in {"dataclasses", "typing", "__future__", "math", "bisect"}:
            for a in node.names:
                if a.name == "*" or (a.asname or a.name) in schemas or (
                        (a.asname or a.name) == "dataclass" and not (node.module == "dataclasses" and a.name == "dataclass" and a.asname is None)):
                    raise RecordError("import rebinds a record schema", node.lineno)
        elif isinstance(node, ast.Import) and len(node.names) == 1 and node.names[0].name in {"sys", "math"} and node.names[0].asname is None:
            pass
        elif isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
            pass
        else:
            raise RecordError("record modules require closed declarations without initialization code", node.lineno)
    # List-bearing records are read-only values in the model. Reject all
    # field writes in their modules. Owned local sort/append/prefix deletion
    # are checked by the encoder, including rejection of borrowed aliases.
    # Guards recursively snapshot fields; frozen=True alone is not deep immutability.
    if any(isinstance(t, ast.Subscript) for fs in schemas.values() for _, t in fs):
        for n in ast.walk(module):
            if (isinstance(n, (ast.Subscript, ast.Attribute)) and isinstance(n.ctx, (ast.Store, ast.Del))
                    and not (isinstance(n, ast.Subscript) and isinstance(n.ctx, ast.Del) and isinstance(n.value, ast.Name))
                    or isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr not in {"sort", "append"}
                    and not (isinstance(n.func.value, ast.Name) and n.func.value.id == "math" and n.func.attr == "prod")) :
                raise RecordError("list-bearing record modules are read-only; container mutation/method calls are unsupported", n.lineno)
    return schemas


def record_type(name):
    return "VRec" + name


def record_constructor(name):
    return "VMake" + name


def record_field(name):
    return "vfield" + name
