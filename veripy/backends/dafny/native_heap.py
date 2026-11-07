"""Conservative source effect proofs for validate-then-commit Python boundaries.

This is an effect abstraction, not a value/CPython heap refinement. Every
admitted branch and finite loop history is retained (pure guards are havoc).
Borrowed writes form a monotone trace; validation rejection must have an empty
trace. Type schemas are explicit trusted external contracts, never inferred
purity from a method's spelling. Unknown expressions/statements fail closed.
"""

from __future__ import annotations

import ast
import hashlib
import json
from dataclasses import dataclass, replace

from veripy.backends.base import register_backend
from veripy.backends.dafny.backend import DafnyBackend
from veripy.backends.dafny.encoder import EncodedModule, _err

VERSION = "heap-effects-2"


@dataclass(frozen=True)
class Value:
    kind: str
    borrowed: bool = False
    parts: tuple = ()
    token: str = ""
    fresh_keys: frozenset[str] | None = frozenset()
    field: str = ""
    optional: bool = False
    iteration_failure: bool = False
    iterated_maps: tuple = ()
    iterator_key: int | None = None


SCALAR = Value("scalar")


def join(a, b, node):
    if a.kind != b.kind or len(a.parts) != len(b.parts):
        raise _err(node, "incompatible alias shapes across control flow")
    return Value(
        a.kind,
        a.borrowed or b.borrowed,
        tuple(join(x, y, node) for x, y in zip(a.parts, b.parts)),
        a.token if a.token == b.token else "",
        b.fresh_keys
        if a.fresh_keys is None
        else a.fresh_keys
        if b.fresh_keys is None
        else a.fresh_keys & b.fresh_keys,
        a.field if a.field == b.field else "",
        a.optional or b.optional,
        a.iteration_failure or b.iteration_failure,
        tuple(dict.fromkeys((*a.iterated_maps, *b.iterated_maps))),
        a.iterator_key if a.iterator_key == b.iterator_key else None,
    )


class Effects:
    def __init__(self, fn, schema):
        self.fn, self.schema = fn, schema
        self.lines, self.line_map, self.env = [], {}, {}
        self.guards = set()
        self.serial = 0
        self.events = []
        self.iterations = []
        for arg in fn.args.args:
            self.env[arg.arg] = replace(self.type(arg.annotation, True), token=arg.arg)

    def type(self, node, borrowed=False):
        if isinstance(node, ast.Constant) and node.value is None:
            return SCALAR
        if isinstance(node, ast.Name):
            if node.id == "bool":
                return Value("bool")
            if node.id == "opaque":
                return Value("opaque")
            if node.id in ("str", "int", "float", "None"):
                return SCALAR
            if node.id in self.schema["types"]:
                return Value(node.id, borrowed)
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
            name = node.value.id
            args = (
                node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
            )
            if (
                name in ("dict", "list", "tuple", "iter")
                and len(args)
                == {"dict": 2, "list": 1, "tuple": len(args), "iter": 1}[name]
            ):
                return Value(name, borrowed, tuple(self.type(a, True) for a in args))
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            left, right = (
                self.type(node.left, borrowed),
                self.type(node.right, borrowed),
            )
            if right == SCALAR:
                return replace(left, optional=True)
        raise _err(node, "heap schema requires an exact admitted type")

    def emit(self, text, node=None, indent="  "):
        self.lines.append(indent + text)
        if node is not None:
            self.line_map[len(self.lines)] = node.lineno

    def reject(self, node, indent):
        self.emit(
            "if * { rejected := true; assert writes == []; return; }", node, indent
        )

    def write(self, value, operation, node, indent, safe=False):
        if not value.borrowed:
            return
        if value.kind == "dict":
            self.guards = {
                (root, key) for root, key in self.guards if root != value.token
            }
        identity = (
            operation in ("append", "extend", "or", "setdefault")
            or operation == "update"
            and safe
        )
        evidence = (
            operation in ("append", "extend", "or", "setdefault")
            or operation == "update"
            and safe
        )
        self.events.append(
            {
                "line": node.lineno,
                "operation": operation,
                "field": value.field,
                "identity_preserving": identity,
                "evidence_monotone": evidence,
            }
        )
        # Every actual borrowed mutation is an event, including identity-preserving
        # writes. No assertion says atomicity; Dafny must prove the trace empty.
        self.emit(f"writes := writes + [{node.lineno}];", node, indent)
        self.emit(
            f"assert {'true' if identity else 'false'}; // retained identities",
            node,
            indent,
        )
        self.emit(
            f"assert {'true' if evidence else 'false'}; // evidence only accumulates",
            node,
            indent,
        )

    def expr(self, n, indent):
        if isinstance(n, ast.Name):
            if n.id not in self.env:
                raise _err(
                    n, "unbound heap value; globals/callbacks are not pure by default"
                )
            return self.env[n.id]
        if isinstance(n, ast.Constant):
            return Value("bool") if type(n.value) is bool else SCALAR
        if isinstance(n, ast.Attribute):
            receiver = self.expr(n.value, indent)
            if receiver.optional:
                # Reading a field of None raises AttributeError.
                self.reject(n, indent)
            fields = self.schema["types"].get(receiver.kind, {}).get("fields", {})
            if n.attr not in fields:
                raise _err(n, "attribute missing from explicit external type contract")
            return replace(
                self.type(
                    ast.parse(fields[n.attr], mode="eval").body, receiver.borrowed
                ),
                field=n.attr,
            )
        if isinstance(n, ast.Subscript):
            receiver = self.expr(n.value, indent)
            if receiver.optional:
                self.reject(n, indent)
            self.expr(n.slice, indent)
            if receiver.kind == "dict":
                # A valid ordinary builtin dict may reject on missing keys. This
                # exception is part of the abstract exceptional frame.
                self.reject(n, indent)
                return receiver.parts[1]
            if (
                receiver.kind in ("tuple", "list")
                and isinstance(n.slice, ast.Constant)
                and type(n.slice.value) is int
            ):
                if receiver.kind == "list":
                    self.reject(n, indent)
                    return receiver.parts[0]
                if not -len(receiver.parts) <= n.slice.value < len(receiver.parts):
                    raise _err(n, "constant tuple index out of bounds")
                return receiver.parts[n.slice.value]
            raise _err(
                n, "only dictionary reads and constant tuple projections supported"
            )
        if isinstance(n, (ast.Tuple, ast.List)):
            values = []
            for item in n.elts:
                if isinstance(item, ast.Starred):
                    iterable = self.expr(item.value, indent)
                    if iterable.iteration_failure:
                        self.reject(item, indent)
                    values.append(self.element(iterable, item))
                else:
                    values.append(self.expr(item, indent))
            values = tuple(values)
            if isinstance(n, ast.Tuple):
                return Value("tuple", parts=values)
            if not values:
                return Value("empty-list")
            value = values[0]
            for other in values[1:]:
                value = join(value, other, n)
            return Value(
                "list", parts=(value,), token=f"literal{n.lineno}_{n.col_offset}"
            )
        if isinstance(n, ast.Dict) and not n.keys:
            return Value("empty-dict")
        if isinstance(n, ast.Starred):
            return self.expr(n.value, indent)
        if isinstance(n, ast.BoolOp):
            values = [self.expr(x, indent) for x in n.values]
            nonempty = [v for v in values if v.kind != "empty-dict"]
            if not nonempty:
                return Value("empty-dict")
            value = nonempty[0]
            for other in nonempty[1:]:
                value = join(value, other, n)
            return (
                replace(value, optional=False) if len(nonempty) < len(values) else value
            )
        if isinstance(n, ast.Compare):
            self.expr(n.left, indent)
            for item in n.comparators:
                self.expr(item, indent)
            return Value("bool")
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.Not):
            self.expr(n.operand, indent)
            return Value("bool")
        if isinstance(n, ast.JoinedStr):
            for item in n.values:
                if isinstance(item, ast.FormattedValue):
                    formatted = self.expr(item.value, indent)
                    if formatted.kind not in ("scalar", "bool"):
                        raise _err(
                            item,
                            "formatting requires exact primitive metadata, not opaque objects",
                        )
                    if item.format_spec is not None:
                        self.expr(item.format_spec, indent)
                        # Any specification may be invalid for the formatted
                        # primitive (ValueError/TypeError) after prior writes.
                        self.reject(item, indent)
            return SCALAR
        if isinstance(n, ast.Call):
            if isinstance(n.func, ast.Name) and n.func.id == "zip":
                values = [self.expr(x, indent) for x in n.args]
                if (
                    len(n.keywords) != 1
                    or n.keywords[0].arg != "strict"
                    or not isinstance(n.keywords[0].value, ast.Constant)
                    or n.keywords[0].value.value is not True
                ):
                    raise _err(n, "zip requires strict=True")
                self.reject(n, indent)
                return Value(
                    "iter",
                    parts=(
                        Value("tuple", parts=tuple(self.element(x, n) for x in values)),
                    ),
                    iteration_failure=True,
                    iterated_maps=tuple(
                        dict.fromkeys(
                            m for value in values for m in value.iterated_maps
                        )
                    ),
                )
            if not isinstance(n.func, ast.Attribute):
                raise _err(n, "unknown call: no implicit helper purity")
            receiver = self.expr(n.func.value, indent)
            if receiver.optional:
                self.reject(n, indent)
            args = [self.expr(x, indent) for x in n.args]
            if n.keywords:
                raise _err(n, "method keyword effects unsupported")
            name = n.func.attr
            if (
                receiver.kind == "dict"
                and name in ("items", "keys", "values")
                and not args
            ):
                return Value(
                    "list",
                    parts=(
                        (
                            Value("tuple", parts=receiver.parts)
                            if name == "items"
                            else receiver.parts[0 if name == "keys" else 1]
                        ),
                    ),
                    iterated_maps=(receiver,),
                    iterator_key=0
                    if name == "items"
                    else -1
                    if name == "keys"
                    else None,
                )
            methods = (
                self.schema["types"].get(receiver.kind, {}).get("pure_methods", {})
            )
            if name in methods and not args:
                return self.type(
                    ast.parse(methods[name], mode="eval").body, receiver.borrowed
                )
            if (
                name in ("append", "extend")
                and receiver.kind == "list"
                and len(args) == 1
            ):
                if name == "extend" and args[0].kind not in ("list", "iter", "tuple"):
                    raise _err(n, "extend requires an admitted iterable")
                self.write(receiver, name, n, indent)
                if name == "extend" and args[0].iteration_failure:
                    self.reject(n, indent)
                if not receiver.borrowed:
                    added = args[0] if name == "append" else self.element(args[0], n)
                    self.set_shape(receiver, (join(receiver.parts[0], added, n),))
                return SCALAR
            if name == "setdefault" and receiver.kind == "dict" and len(args) == 2:
                if args[1].kind != "empty-list" or receiver.parts[1].kind != "list":
                    raise _err(
                        n, "setdefault admitted only for empty-list initialization"
                    )
                self.write(receiver, name, n, indent)
                self.iterator_mutation(receiver, n, indent, key=n.args[0])
                if not receiver.borrowed:
                    self.set_capability(receiver, frozenset())
                return receiver.parts[1]
            if (
                name == "update"
                and receiver.kind == "dict"
                and len(args) == 1
                and args[0].kind == "dict"
            ):
                if not receiver.borrowed:
                    self.set_shape(
                        receiver,
                        tuple(
                            join(a, b, n) for a, b in zip(receiver.parts, args[0].parts)
                        ),
                    )
                    inherited = args[0].fresh_keys
                    capability = (
                        inherited
                        if receiver.fresh_keys is None
                        else receiver.fresh_keys
                        if inherited is None
                        else receiver.fresh_keys & inherited
                    )
                    self.set_capability(receiver, capability)
                self.write(
                    receiver,
                    name,
                    n,
                    indent,
                    safe=bool(receiver.token)
                    and (
                        args[0].fresh_keys is None
                        or receiver.token in args[0].fresh_keys
                    ),
                )
                self.iterator_mutation(receiver, n, indent)
                return SCALAR
            raise _err(n, "method has no admitted effect or external purity contract")
        raise _err(
            n,
            f"unsupported heap expression {type(n).__name__}; hidden effects are not erased",
        )

    def element(self, value, n):
        if value.kind in ("list", "iter"):
            return value.parts[0]
        # A tuple used as an iterable is a finite union, preserving references.
        if value.kind == "tuple" and value.parts:
            result = value.parts[0]
            for item in value.parts[1:]:
                if item.kind == "list":
                    item = self.element(item, n)
                result = join(result, item, n)
            return result
        raise _err(n, "iteration requires admitted container element shape")

    def bind(self, target, value, indent):
        if isinstance(target, ast.Name):
            # Any rebinding of a key invalidates guards that mention the name.
            self.guards = {
                (root, key)
                for root, key in self.guards
                if "Name(id=" + repr(target.id) + "," not in key
            }
            self.iterations = [
                (mapping, None if key == target.id else key)
                for mapping, key in self.iterations
            ]
            self.env[target.id] = value
        elif (
            isinstance(target, (ast.Tuple, ast.List))
            and value.kind == "tuple"
            and len(target.elts) == len(value.parts)
        ):
            for name, item in zip(target.elts, value.parts):
                self.bind(name, item, indent)
        elif isinstance(target, ast.Attribute):
            receiver = self.expr(target.value, indent)
            self.expr(target, indent)
            self.write(receiver, "replace", target, indent)
        elif isinstance(target, ast.Subscript):
            receiver = self.expr(target.value, indent)
            self.expr(target.slice, indent)
            if receiver.kind != "dict":
                raise _err(target, "heap writes require a dictionary")
            if receiver.borrowed:
                self.write(receiver, "replace", target, indent)
            self.iterator_mutation(receiver, target, indent, key=target.slice)
            if not receiver.borrowed:
                self.set_shape(
                    receiver,
                    (receiver.parts[0], join(receiver.parts[1], value, target)),
                )
                key = ast.dump(target.slice)
                guarded_roots = frozenset(
                    root for root, guarded in self.guards if guarded == key
                )
                capability = (
                    guarded_roots
                    if receiver.fresh_keys is None
                    else receiver.fresh_keys & guarded_roots
                )
                self.set_capability(receiver, capability)
        else:
            raise _err(target, "unsupported assignment target")

    def iterator_mutation(self, receiver, node, indent, key=None):
        """Builtin dict iterators may raise after a size-changing write.

        A setdefault/subscript of that iterator's unchanged current key cannot
        change its size even if two borrowed map references alias. Other writes
        conservatively retain the possible exceptional exit after the effect.
        """
        for mapping, current_key in self.iterations:
            can_alias = receiver.borrowed == mapping.borrowed and (
                receiver.borrowed
                or not receiver.token
                or not mapping.token
                or receiver.token == mapping.token
            )
            same_key = isinstance(key, ast.Name) and key.id == current_key
            if can_alias and not same_key:
                self.reject(node, indent)
                return

    def set_shape(self, receiver, parts):
        def update(alias):
            children = tuple(update(x) for x in alias.parts)
            return replace(
                alias,
                parts=parts
                if alias.token and alias.token == receiver.token
                else children,
            )

        self.env = {name: update(alias) for name, alias in self.env.items()}

    def set_capability(self, receiver, capability):
        def invalidate(alias):
            children = tuple(invalidate(x) for x in alias.parts)
            return replace(
                alias,
                parts=children,
                fresh_keys=capability
                if alias.token and alias.token == receiver.token
                else alias.fresh_keys,
            )

        self.env = {name: invalidate(alias) for name, alias in self.env.items()}

    def block(self, statements, indent):
        for n in statements:
            if isinstance(n, ast.Expr):
                self.expr(n.value, indent)
            elif isinstance(n, ast.AnnAssign):
                if not isinstance(n.target, ast.Name) or n.value is None:
                    raise _err(n, "typed locals require initialized names")
                actual = self.expr(n.value, indent)
                value = self.type(n.annotation)
                if actual.kind in ("empty-list", "empty-dict"):
                    value = replace(
                        value,
                        token=f"local{n.lineno}_{n.col_offset}",
                        fresh_keys=None if value.kind == "dict" else frozenset(),
                    )
                else:
                    value = join(value, actual, n)
                self.bind(n.target, value, indent)
            elif isinstance(n, ast.Assign):
                value = self.expr(n.value, indent)
                for target in n.targets:
                    self.bind(target, value, indent)
            elif isinstance(n, ast.AugAssign):
                value = self.expr(n.target, indent)
                operand = self.expr(n.value, indent)
                if (
                    not isinstance(n.target, ast.Attribute)
                    or not isinstance(n.op, ast.BitOr)
                    or value.kind != "bool"
                    or operand.kind != "bool"
                ):
                    raise _err(n, "only field boolean OR augmentation admitted")
                self.write(self.expr(n.target.value, indent), "or", n, indent)
            elif isinstance(n, ast.Assert):
                self.expr(n.test, indent)
                # Assertion messages are only evaluated on failure; allowing
                # their pure reads on all paths conservatively adds rejection.
                if n.msg is not None:
                    self.expr(n.msg, indent)
                self.reject(n, indent)
            elif isinstance(n, ast.Raise):
                if n.exc is not None and not (
                    isinstance(n.exc, ast.Call)
                    and isinstance(n.exc.func, ast.Name)
                    and n.exc.func.id in ("AssertionError", "ValueError", "KeyError")
                    and not n.exc.keywords
                ):
                    raise _err(n, "only validation exception construction admitted")
                if n.exc is not None:
                    for arg in n.exc.args:
                        self.expr(arg, indent)
                if n.cause is not None:
                    self.expr(n.cause, indent)
                self.emit("rejected := true; assert writes == []; return;", n, indent)
            elif isinstance(n, ast.Return):
                if n.value is not None:
                    self.expr(n.value, indent)
                self.emit("return;", n, indent)
            elif isinstance(n, ast.If):
                self.expr(n.test, indent)
                before, guards = dict(self.env), set(self.guards)
                # Fresh insertion capability is tied to the exact borrowed map
                # and key, never to variable names or statement positions.
                if (
                    isinstance(n.test, ast.Compare)
                    and len(n.test.ops) == 1
                    and isinstance(n.test.ops[0], ast.NotIn)
                ):
                    container = self.expr(n.test.comparators[0], indent)
                    if (
                        container.borrowed
                        and container.kind == "dict"
                        and container.token
                        and isinstance(n.test.left, ast.Name)
                    ):
                        self.guards.add((container.token, ast.dump(n.test.left)))
                self.emit("if * {", n, indent)
                self.block(n.body, indent + "  ")
                body = dict(self.env)
                body_guards = set(self.guards)
                self.env, self.guards = dict(before), guards
                self.emit("} else {", n, indent)
                self.block(n.orelse, indent + "  ")
                other = dict(self.env)
                self.guards &= body_guards
                self.emit("}", n, indent)
                # Names assigned on just one branch remain unavailable later.
                self.env = {
                    key: join(body[key], other[key], n)
                    for key in body.keys() & other.keys()
                }
            elif isinstance(n, ast.For):
                value = self.expr(n.iter, indent)
                self.bind(n.target, self.element(value, n), indent)
                outer_iterations = list(self.iterations)
                key = (
                    n.target
                    if value.iterator_key == -1
                    else n.target.elts[0]
                    if value.iterator_key == 0
                    and isinstance(n.target, (ast.Tuple, ast.List))
                    else None
                )
                current_key = key.id if isinstance(key, ast.Name) else None
                self.iterations += [
                    (mapping, current_key) for mapping in value.iterated_maps
                ]
                self.widen_loop(n, indent)
                self.serial += 1
                serial = self.serial
                self.emit(f"var frame{serial} := writes;", n, indent)
                pos = len(self.lines)
                self.emit("while *", n, indent)
                self.emit("  decreases *", n, indent)
                invariant_pos = len(self.lines)
                self.emit("{", n, indent)
                if value.iteration_failure:
                    self.reject(n, indent + "  ")
                self.block(n.body, indent + "  ")
                self.emit("}", n, indent)
                if value.iteration_failure:
                    self.reject(n, indent)
                self.iterations = [
                    (mapping, key if (mapping, key) in self.iterations else None)
                    for mapping, key in outer_iterations
                ]
                # Frames are mechanically derived from emitted write effects;
                # a loop with writes gets only the sound prefix invariant.
                has_write = any("writes := writes +" in x for x in self.lines[pos:])
                invariant = (
                    f"  invariant frame{serial} <= writes"
                    if has_write
                    else f"  invariant writes == frame{serial}"
                )
                self.lines.insert(invariant_pos, indent + invariant)
                self.line_map = {
                    (k + 1 if k > invariant_pos else k): v
                    for k, v in self.line_map.items()
                }
                if n.orelse:
                    self.block(n.orelse, indent)
            elif isinstance(n, ast.Continue):
                self.emit("continue;", n, indent)
            elif isinstance(n, ast.Pass):
                pass
            else:
                raise _err(n, f"unsupported heap statement {type(n).__name__}")

    def widen_loop(self, node, indent):
        """Join zero/one/many iterations before emitting the loop body.

        A fresh alias can become borrowed at the end of one iteration and be
        written at the beginning of the next. A single AST walk misses that.
        Finite provenance domains must reach a fixed point or fail closed.
        """
        entry = dict(self.env)
        saved_lines, saved_map = self.lines, self.line_map
        saved_events, saved_serial = self.events, self.serial
        saved_guards = set(self.guards)
        saved_iterations = list(self.iterations)
        try:
            for _ in range(32):
                self.lines, self.line_map, self.events = [], {}, []
                self.serial = saved_serial
                self.guards = set(saved_guards)
                self.iterations = [
                    (mapping, key if (mapping, key) in self.iterations else None)
                    for mapping, key in saved_iterations
                ]
                self.env = dict(entry)
                self.block(node.body, indent)
                merged = {
                    key: join(value, self.env.get(key, value), node)
                    for key, value in entry.items()
                }
                if merged == entry:
                    self.env = merged
                    return
                entry = merged
            raise _err(node, "heap alias analysis did not converge")
        finally:
            self.lines, self.line_map = saved_lines, saved_map
            self.events, self.serial = saved_events, saved_serial
            # Guards killed by a possible loop iteration must not survive.
            self.guards &= saved_guards

    def encode(self):
        self.emit(
            f"method {self.fn.name}() returns (rejected: bool, writes: seq<int>)",
            self.fn,
            "",
        )
        self.emit("  ensures rejected ==> writes == []", self.fn, "")
        self.emit("  decreases *", self.fn, "")
        self.emit("{", indent="")
        self.emit("rejected := false; writes := [];", self.fn)
        self.block(self.fn.body, "  ")
        self.emit("}", indent="")


class DafnyHeapBackend(DafnyBackend):
    name = "dafny-heap"
    preamble_version = VERSION

    def encode(self, source, specs, *, module_name, proof_lemmas):
        schema_lines = [
            line.split("# heap-schema:", 1)[1].strip()
            for line in source.splitlines()
            if line.startswith("# heap-schema:")
        ]
        if not schema_lines:
            raise _err(
                ast.parse(source),
                "missing explicit # heap-schema external type contract",
            )
        schema = json.loads("\n".join(schema_lines))
        if set(schema) != {"types"}:
            raise ValueError("heap schema expects only types")
        tree = ast.parse(source)
        for binding in ast.walk(tree):
            if isinstance(binding, ast.alias) and binding.name == "*":
                raise _err(
                    binding,
                    "wildcard import may shadow heap builtins or contracted types",
                )
            name = (
                binding.id
                if isinstance(binding, ast.Name)
                and isinstance(binding.ctx, (ast.Store, ast.Del))
                else binding.arg
                if isinstance(binding, ast.arg)
                else binding.name
                if isinstance(
                    binding, (ast.FunctionDef, ast.ClassDef, ast.ExceptHandler)
                )
                else (binding.asname or binding.name).split(".")[0]
                if isinstance(binding, ast.alias)
                else binding.attr
                if isinstance(binding, ast.Attribute)
                and isinstance(binding.ctx, (ast.Store, ast.Del))
                else None
            )
            if name in ("zip", "AssertionError", "ValueError", "KeyError"):
                raise _err(
                    binding, f"binding shadows builtin {name} used by heap lowering"
                )
        lines, line_map, methods, events = (
            [f"// {VERSION} source {hashlib.sha256(source.encode()).hexdigest()}"],
            {},
            [],
            [],
        )
        for spec in specs.functions:
            if any(c.kind != "verified" for c in spec.clauses):
                raise ValueError(
                    "heap backend has fixed rejection/identity/accumulation contracts; scalar clauses unsupported"
                )
            matches = [
                n
                for n in tree.body
                if isinstance(n, ast.FunctionDef) and n.name == spec.name
            ]
            if len(matches) != 1:
                raise ValueError("heap targets must be unique top-level functions")
            fn = matches[0]
            if (
                fn.decorator_list
                or fn.args.vararg
                or fn.args.kwarg
                or fn.args.kwonlyargs
                or fn.args.posonlyargs
                or fn.args.defaults
                or fn.args.kw_defaults
                or getattr(fn, "type_params", ())
            ):
                raise _err(fn, "heap function signature unsupported")
            encoder = Effects(fn, schema)
            encoder.encode()
            offset = len(lines)
            lines.extend(encoder.lines)
            line_map.update({k + offset: v for k, v in encoder.line_map.items()})
            methods.append(fn.name)
            events.extend(encoder.events)
        if not methods:
            raise ValueError("heap verification requires nonempty annotated targets")
        lines.append("// ---- STUB END: proof additions go below ----")
        encoded = EncodedModule(
            "\n".join(lines) + "\n", line_map, methods, {n: n for n in methods}
        )
        encoded.translation = {
            "version": VERSION,
            "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "external_type_contract": schema,
            "write_effects": events,
            "theorem": "validation rejection has no borrowed writes; retained identities; monotone evidence",
            "assumptions": [
                "exact builtin containers, scalar metadata and externally contracted passive model fields/methods",
                "stable imports/types, no reentrant or concurrent mutations, no hostile descriptors/equality",
                "finite histories; MemoryError, async interruption and interpreter failure excluded",
                "effect lowering trusted; metadata guard truth and business compatibility not proved",
            ],
        }
        return encoded


register_backend("dafny-heap", DafnyHeapBackend)
