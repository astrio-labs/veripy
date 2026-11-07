"""Opt-in source lowering for closed immutable scalar/timedelta instance methods.

This is a deliberately restricted extension. It keeps executable method ASTs,
checks native operand types before mapping timedelta values to exact integer
microseconds, and proves overflow freedom for every admitted timedelta product.
It does not encode mutable objects, arbitrary descriptors, imports or the ORM.
"""

from __future__ import annotations

import ast
import copy
import hashlib

from veripy.backends.base import register_backend
from veripy.backends.dafny.encoder import EncodeError, _err, _module_shadow_check
from veripy.backends.dafny.outcomes import (
    OutcomeBackend,
    OutcomeEncoder,
    encode_outcomes,
)
from veripy.frontend.parse import Clause, ModuleSpecs

TD_MIN = -999999999 * 86400 * 1000000
TD_MAX = (999999999 * 86400 + 86399) * 1000000 + 999999
VERSION = "native-scalar-timedelta-2"

PREAMBLE = """
// Exact builtin int bit_length: sign does not contribute a bit.
function NativeBitLengthNat(n: int): int
  requires n >= 0
  ensures NativeBitLengthNat(n) >= 0
  decreases n
{
  if n == 0 then 0 else 1 + NativeBitLengthNat(n / 2)
}
function NativeBitLength(n: int): int
{ NativeBitLengthNat(if n < 0 then -n else n) }
"""


class NativeTypes:
    """Reject source operations whose native type semantics differ from ints."""

    def __init__(self, fields, node):
        self.fields = fields
        self.locals = {
            arg.arg: arg.annotation.id
            for arg in node.args.args[1:]
            if isinstance(arg.annotation, ast.Name)
        }
        self.returns = (
            "None"
            if isinstance(node.returns, ast.Constant) and node.returns.value is None
            else getattr(node.returns, "id", None)
        )

    def infer(self, node):
        kind = None
        if isinstance(node, ast.Constant):
            kind = {int: "int", bool: "bool", str: "str", type(None): "None"}.get(
                type(node.value)
            )
        elif isinstance(node, ast.Name):
            kind = self.locals.get(node.id)
        elif (
            isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == "self"
        ):
            kind = self.fields.get(node.attr)
        elif isinstance(node, ast.UnaryOp):
            operand = self.infer(node.operand)
            if isinstance(node.op, ast.Not) and operand == "bool":
                kind = "bool"
            elif isinstance(node.op, ast.USub) and operand == "int":
                kind = "int"
        elif isinstance(node, ast.BinOp):
            left, right = self.infer(node.left), self.infer(node.right)
            if (
                left == right == "int"
                and isinstance(
                    node.op,
                    (
                        ast.Add,
                        ast.Sub,
                        ast.Mult,
                        ast.FloorDiv,
                        ast.Mod,
                        ast.Pow,
                        ast.LShift,
                    ),
                )
                or left == right == "timedelta"
                and isinstance(node.op, ast.FloorDiv)
            ):
                kind = "int"
            elif isinstance(node.op, ast.Mult) and (left, right) in [
                ("timedelta", "int"),
                ("int", "timedelta"),
            ]:
                kind = "timedelta"
        elif isinstance(node, ast.Compare):
            kinds = [self.infer(n) for n in [node.left, *node.comparators]]
            if (
                len(set(kinds)) == 1
                and kinds[0] in ("int", "timedelta", "bool", "str")
                and all(
                    isinstance(
                        op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Eq, ast.NotEq)
                    )
                    for op in node.ops
                )
            ):
                kind = "bool"
        elif isinstance(node, ast.BoolOp):
            if all(self.infer(n) == "bool" for n in node.values):
                kind = "bool"
        elif isinstance(node, ast.Call) and not node.keywords:
            if isinstance(node.func, ast.Name) and node.func.id == "timedelta":
                if (
                    len(node.args) == 1
                    and isinstance(node.args[0], ast.Constant)
                    and type(node.args[0].value) is int
                    and node.args[0].value == 0
                ):
                    kind = "timedelta"
            elif (
                isinstance(node.func, ast.Attribute)
                and node.func.attr == "bit_length"
                and not node.args
                and self.infer(node.func.value) == "int"
            ):
                kind = "int"
            elif (
                isinstance(node.func, ast.Name)
                and node.func.id in ("min", "max")
                and len(node.args) == 2
            ):
                kinds = [self.infer(n) for n in node.args]
                if kinds[0] == kinds[1] and kinds[0] in ("int", "timedelta"):
                    kind = kinds[0]
        if kind is None:
            raise _err(
                node,
                "native scalar operand/call/type is outside the admitted timedelta fragment",
            )
        node._native_type = kind
        return kind

    def block(self, statements):
        for stmt in statements:
            if (
                isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and type(stmt.value.value) is str
            ):
                continue
            if isinstance(stmt, ast.If):
                if self.infer(stmt.test) != "bool":
                    raise _err(stmt, "native conditions require bool")
                if any(
                    isinstance(n, ast.BinOp)
                    and (
                        isinstance(n.op, ast.LShift)
                        or getattr(n, "_native_type", None) == "timedelta"
                    )
                    for n in ast.walk(stmt.test)
                ):
                    raise _err(
                        stmt,
                        "potentially failing native arithmetic is admitted only in eager return expressions",
                    )
                self.block(stmt.body)
                self.block(stmt.orelse)
            elif isinstance(stmt, ast.Return):
                actual = self.infer(stmt.value) if stmt.value is not None else "None"
                if actual != self.returns:
                    raise _err(stmt, "native return type does not match annotation")
                if (
                    stmt.value is not None
                    and any(
                        isinstance(n, ast.BinOp) and isinstance(n.op, ast.LShift)
                        for n in ast.walk(stmt.value)
                    )
                    and any(
                        # Short-circuiting forms (including chained comparisons)
                        # may skip a shift that the model always evaluates.
                        isinstance(n, (ast.BoolOp, ast.IfExp))
                        or isinstance(n, ast.Compare)
                        and len(n.ops) > 1
                        or isinstance(n, ast.BinOp)
                        and isinstance(n.op, (ast.FloorDiv, ast.Mod, ast.Pow))
                        for n in ast.walk(stmt.value)
                    )
                ):
                    raise _err(
                        stmt,
                        "shift outcomes require eager expressions without division or powers",
                    )
            elif isinstance(stmt, ast.Raise):
                exc = stmt.exc
                if (
                    stmt.cause is not None
                    or not isinstance(exc, ast.Call)
                    or not isinstance(exc.func, ast.Name)
                    or exc.func.id != "ValueError"
                    or exc.keywords
                    or len(exc.args) != 1
                    or not isinstance(exc.args[0], ast.Constant)
                    or type(exc.args[0].value) is not str
                ):
                    raise _err(
                        stmt, "native fragment admits only literal ValueError messages"
                    )
            elif isinstance(stmt, ast.Pass):
                pass
            else:
                raise _err(
                    stmt,
                    "native immutable methods admit only branches, returns and ValueError; writes/other effects are unsupported",
                )


def lower_native(source, specs):
    module = ast.parse(source)
    _module_shadow_check(module)
    targets = {(s.name, s.lineno): s for s in specs.functions}
    imports = {}
    selected = []
    # Stable explicit stdlib bindings only; do not execute initializers.
    for node in module.body:
        if (
            isinstance(node, ast.ImportFrom)
            and node.level == 0
            and node.module
            in ("dataclasses", "datetime", "email.utils", "typing", "__future__")
        ):
            for alias in node.names:
                name = alias.asname or alias.name
                if alias.asname or name == "*" or name in imports:
                    raise _err(
                        node, "native imports must be unaliased, unique, and closed"
                    )
                imports[name] = (node.module, alias.name)
        elif isinstance(node, ast.ClassDef):
            if any(
                isinstance(n, ast.FunctionDef) and (n.name, n.lineno) in targets
                for n in node.body
            ):
                selected.append(node)
            else:
                raise _err(
                    node, "unmodeled class declarations are outside the native closure"
                )
        elif isinstance(node, ast.FunctionDef):
            if (
                node.decorator_list
                or node.args.defaults
                or any(v is not None for v in node.args.kw_defaults)
                or (node.name, node.lineno) in targets
            ):
                raise _err(
                    node,
                    "native closure permits only undecorated, unselected collateral functions without defaults",
                )
        elif (
            isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and type(node.value.value) is str
        ):
            pass
        else:
            raise _err(node, "native module effects or rebinding are unsupported")
    if imports.get("dataclass") != ("dataclasses", "dataclass") or imports.get(
        "timedelta"
    ) != ("datetime", "timedelta"):
        raise EncodeError(
            "native methods require exact unaliased dataclass/timedelta imports"
        )
    if not selected:
        raise EncodeError(
            "native backend requires explicitly specified immutable instance methods"
        )
    if any(
        isinstance(n, (ast.ClassDef, ast.FunctionDef)) and n.name in imports
        for n in module.body
    ):
        raise EncodeError("native declaration shadows a semantic dependency")
    bodies = [
        ast.ImportFrom(
            module="dataclasses", names=[ast.alias(name="dataclass")], level=0
        )
    ]
    lowered_specs = []
    names = set()
    for cls in selected:
        if (
            cls.name in names
            or cls.bases
            or cls.keywords
            or len(cls.decorator_list) != 1
            or getattr(cls, "type_params", [])
        ):
            raise _err(
                cls,
                "native records require unique closed classes without inheritance/type parameters",
            )
        names.add(cls.name)
        decorator = cls.decorator_list[0]
        if (
            not isinstance(decorator, ast.Call)
            or not isinstance(decorator.func, ast.Name)
            or decorator.func.id != "dataclass"
            or decorator.args
        ):
            raise _err(
                cls, "native records require dataclass(frozen=True[, slots=bool])"
            )
        options = {
            k.arg: k.value.value
            for k in decorator.keywords
            if isinstance(k.value, ast.Constant) and type(k.value.value) is bool
        }
        if (
            len(options) != len(decorator.keywords)
            or options.get("frozen") is not True
            or set(options) - {"frozen", "slots"}
        ):
            raise _err(
                cls, "native records require frozen=True and only literal slots option"
            )
        fields = {}
        declarations = []
        methods = []
        for item in cls.body:
            if (
                isinstance(item, ast.Expr)
                and isinstance(item.value, ast.Constant)
                and type(item.value.value) is str
            ):
                continue
            if (
                isinstance(item, ast.AnnAssign)
                and isinstance(item.target, ast.Name)
                and item.value is None
                and isinstance(item.annotation, ast.Name)
                and item.annotation.id in ("timedelta", "int", "bool")
            ):
                if item.target.id in fields:
                    raise _err(item, "duplicate native field")
                if item.target.id.startswith("__") and item.target.id.endswith("__"):
                    raise _err(item, "native fields cannot replace Python special attributes")
                fields[item.target.id] = item.annotation.id
                field = copy.deepcopy(item)
                if item.annotation.id == "timedelta":
                    field.annotation.id = "int"
                declarations.append(field)
            elif isinstance(item, ast.FunctionDef):
                methods.append(item)
            else:
                raise _err(
                    item,
                    "native classes admit fields and explicitly specified methods only",
                )
        if not fields:
            raise _err(cls, "native snapshot requires fields")
        snapshot = copy.deepcopy(cls)
        snapshot.body = declarations
        snapshot.decorator_list = [
            ast.Call(
                func=ast.Name(id="dataclass", ctx=ast.Load()),
                args=[],
                keywords=[ast.keyword(arg="frozen", value=ast.Constant(True))],
            )
        ]
        bodies.append(snapshot)
        for method in methods:
            # Record reads and dataclass construction use Python's ordinary
            # attribute machinery. A user hook could replace those semantics
            # even though its separately encoded body is pure and proved.
            if (method.name.startswith("__") and method.name.endswith("__")
                    and method.name != "__post_init__"):
                raise _err(method, "native methods cannot override Python special methods")
            key = (method.name, method.lineno)
            if (
                key not in targets
                or method.decorator_list
                or getattr(method, "type_params", [])
                or method.args.vararg
                or method.args.kwarg
                or method.args.kwonlyargs
                or method.args.posonlyargs
                or method.args.defaults
                or not method.args.args
                or method.args.args[0].arg != "self"
            ):
                raise _err(
                    method,
                    "native methods require explicit contracts and simple positional self signatures",
                )
            if method.name in fields:
                raise _err(method, "native method shadows field")
            if any(
                arg.arg in ("timedelta", "dataclass")
                or arg.arg == "self"
                and index > 0
                or index > 0
                and (
                    not isinstance(arg.annotation, ast.Name)
                    or arg.annotation.id not in ("int", "bool")
                )
                for index, arg in enumerate(method.args.args)
            ):
                raise _err(
                    method,
                    "native parameters require exact int/bool types without reserved bindings",
                )
            NativeTypes(fields, method).block(method.body)
            lowered = copy.deepcopy(method)
            lowered.name = cls.name + "_" + method.name
            lowered.col_offset = 0
            lowered.args.args[0].annotation = ast.Name(id=cls.name, ctx=ast.Load())
            if (
                isinstance(lowered.returns, ast.Name)
                and lowered.returns.id == "timedelta"
            ):
                lowered.returns.id = "int"
            if ast.dump(
                ast.Module(body=method.body, type_ignores=[]), include_attributes=False
            ) != ast.dump(
                ast.Module(body=lowered.body, type_ignores=[]), include_attributes=False
            ):
                raise _err(
                    method,
                    "native lowering must preserve every executable method-body AST",
                )
            spec = copy.deepcopy(targets[key])
            spec.name = lowered.name
            # These are native type domains, not business preconditions.
            for name, kind in fields.items():
                if kind == "timedelta":
                    expr = f"{TD_MIN} <= self.{name} <= {TD_MAX}"
                    spec.clauses.append(
                        Clause(
                            kind="requires",
                            raw=expr,
                            desugared=expr,
                            line=method.lineno,
                        )
                    )
            bodies.append(lowered)
            lowered_specs.append(spec)
    if len(lowered_specs) != len(targets):
        raise EncodeError(
            "native specs must identify only the admitted instance methods"
        )
    lowered_module = ast.fix_missing_locations(ast.Module(body=bodies, type_ignores=[]))
    metadata = {
        "version": VERSION,
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "unit": "exact integer microseconds",
        "body_ast_preserved": True,
        "methods": [
            {
                "class_name": cls.name,
                "method": m.name,
                "lowered_function": cls.name + "_" + m.name,
                "line": m.lineno,
                "body_sha256": hashlib.sha256(
                    ast.dump(
                        ast.Module(body=m.body, type_ignores=[]),
                        include_attributes=False,
                    ).encode()
                ).hexdigest(),
            }
            for cls in selected
            for m in cls.body
            if isinstance(m, ast.FunctionDef)
        ],
        "assumptions": [
            "exact builtin field and parameter types; stable module bindings; immutable snapshots; no hostile object.__setattr__ or monkeypatching",
            "frontend/microsecond/bit_length translation is trusted and tested, not a mechanized CPython refinement proof",
            "resource exhaustion and exception messages/tracebacks are outside the theorem",
        ],
        "lowered_source": ast.unparse(lowered_module),
    }
    return lowered_module, ModuleSpecs(functions=lowered_specs, orphans=[]), metadata


class NativeEncoder(OutcomeEncoder):
    def _infer(self, node):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id == "timedelta":
                return "int"
            if (
                isinstance(node.func, ast.Attribute)
                and node.func.attr == "bit_length"
                and self._infer(node.func.value) == "int"
            ):
                return "int"
        return super()._infer(node)

    def _call(self, node):
        if isinstance(node.func, ast.Name) and node.func.id == "timedelta":
            if (
                node.keywords
                or len(node.args) != 1
                or not isinstance(node.args[0], ast.Constant)
                or type(node.args[0].value) is not int
                or node.args[0].value != 0
            ):
                raise _err(node, "only exact timedelta(0) is admitted")
            return "0"
        if isinstance(node.func, ast.Attribute) and node.func.attr == "bit_length":
            if node.args or node.keywords or self._infer(node.func.value) != "int":
                raise _err(node, "bit_length requires an exact int and no arguments")
            return f"NativeBitLength({self.expr(node.func.value)})"
        return super()._call(node)

    def expr(self, node):
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            if self._infer(node.left) != "int" or self._infer(node.right) != "int":
                raise _err(node, "native left shift requires exact integer operands")
            return f"({self.expr(node.left)} * PyPow(2, {self.expr(node.right)}))"
        return super().expr(node)

    def stmt(self, stmt, indent):
        if isinstance(stmt, ast.Return) and stmt.value is not None:
            for clause in self._proofs_by_stmt.pop(id(stmt), []):
                self._emit_proof(clause, indent)
            # Operations are pure and eager in this admitted expression subset,
            # so checks follow Python's evaluation order: an earlier product's
            # OverflowError precedes a later negative shift's ValueError.
            for node in _evaluation_order(stmt.value):
                if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
                    self.emit(f"{indent}if {self.expr(node.right)} < 0 {{", node.lineno)
                    self.emit(
                        f"{indent}  {self.error_name} := true; return;", node.lineno
                    )
                    self.emit(f"{indent}}}")
                elif (
                    isinstance(node, ast.BinOp)
                    and getattr(node, "_native_type", None) == "timedelta"
                ):
                    value = self.expr(node)
                    self.emit(
                        f"{indent}assert {TD_MIN} <= {value} <= {TD_MAX};", node.lineno
                    )
        return super().stmt(stmt, indent)


def _evaluation_order(node):
    """Post-order: operands (in field order) are evaluated before their operation."""
    for child in ast.iter_child_nodes(node):
        yield from _evaluation_order(child)
    yield node


class NativeBackend(OutcomeBackend):
    name = "dafny-native"

    @property
    def preamble_version(self):
        return super().preamble_version + "-" + VERSION

    def encode(self, source, specs, *, module_name, proof_lemmas):
        module, lowered_specs, metadata = lower_native(source, specs)
        encoded = encode_outcomes(
            source,
            lowered_specs,
            module_name,
            proof_lemmas,
            module_override=module,
            encoder_class=NativeEncoder,
            preamble_extension=PREAMBLE,
        )
        encoded.translation = metadata
        return encoded

    def verify_artifact(self, artifact, line_map, *, time_limit, extent):
        result = super().verify_artifact(
            artifact, line_map, time_limit=time_limit, extent=extent
        )
        artifact.with_suffix(".prover.log").write_text(result.raw or result.error or "")
        return result


register_backend("dafny-native", NativeBackend)
