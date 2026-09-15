"""Experimental ValueError-outcome backend for typed deterministic functions.

Admits one typed function, explicit ValueError raises, and try/except/else
whose try body is a sequence of int(str) assignments and whose handler raises
ValueError. All other expressions/control flow use the ordinary Dafny encoder.
Scalar, list and None results are supported. Scalar parameter rebinding uses
fresh executable locals, while contracts and old() keep the entry snapshots.
Normal result and exception-class outcomes are proved; exception messages and
traceback/cause objects are not represented in the proof result.
"""
from __future__ import annotations

import ast
import copy
from dataclasses import replace

from veripy.backends.base import register_backend
from veripy.backends.dafny.backend import DafnyBackend
from veripy.backends.dafny import decimal, unicode_strings, regex_strings
from veripy.backends.dafny.encoder import (EncodedModule, EncodeError, _MethodEncoder, _dafny_type,
                      _err, _module_shadow_check, _collect_math_imports, _helper_signatures, _sequence_imports, _checked_defaults)
from veripy.frontend.records import record_schemas, RecordError, record_type, record_constructor, record_field
from veripy.backends.dafny.preamble import PREAMBLE


class OutcomeEncoder(_MethodEncoder):
    def __init__(self, node, spec, *args, **kwargs):
        # Python scalar parameters are local bindings. Keep immutable inputs for
        # contracts/old(), and alpha-rename their executable bindings to locals.
        parameters = {a.arg: a for a in (*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs)}
        rebound = {n.id for n in ast.walk(node) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)} & parameters.keys()
        if rebound:
            if any(not isinstance(parameters[name].annotation, ast.Name) or parameters[name].annotation.id not in {"int", "bool", "str"} for name in rebound):
                raise _err(node, "outcome parameter rebinding supports scalar parameters only")
            if any(isinstance(n, (ast.Lambda, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp, ast.AsyncFunctionDef)) or isinstance(n, ast.FunctionDef) and n is not node for n in ast.walk(node)):
                raise _err(node, "rebound outcome parameters do not support nested scopes")
            used = {n.id for n in ast.walk(node) if isinstance(n, ast.Name)} | set(kwargs.get('reserved_names', ()))
            for clause in spec.clauses:
                if clause.desugared:
                    used.update(n.id for n in ast.walk(ast.parse(clause.desugared, mode='eval')) if isinstance(n, ast.Name))
            names = {}
            for name in sorted(rebound):
                local = name + '_local'
                while local in used:
                    local += '_'
                names[name] = local
                used.add(local)

            class Rename(ast.NodeTransformer):
                def visit_Name(self, n):
                    return ast.copy_location(ast.Name(id=names.get(n.id, n.id), ctx=n.ctx), n)

                def visit_Call(self, n):
                    if isinstance(n.func, ast.Name) and n.func.id == 'old':
                        return n
                    return self.generic_visit(n)

            node, spec = copy.deepcopy(node), copy.deepcopy(spec)
            node.body = [Rename().visit(stmt) for stmt in node.body]
            initializers = [ast.copy_location(ast.Assign(targets=[ast.Name(id=local, ctx=ast.Store())], value=ast.Name(id=name, ctx=ast.Load())), node.body[0]) for name, local in names.items()]
            node.body = initializers + node.body
            ast.fix_missing_locations(node)
            for clause in spec.clauses:
                if clause.kind in {'invariant', 'decreases', 'proof'} and clause.desugared:
                    clause.desugared = ast.unparse(Rename().visit(ast.parse(clause.desugared, mode='eval')))
        super().__init__(node, spec, *args, **kwargs)
        self.tagged = bool(self.exceptions)
        self.exception_tags = {"ValueError":1, **{name:i+2 for i,name in enumerate(sorted(self.exceptions))}}
        self.handler_target = None
        # The specialized conversion-try lowering declares these fresh targets
        # before its failure label. Generic branch hoisting must not independently
        # infer or redeclare them across the try/else paths.
        self._managed_conversion_locals = {
            item.targets[0].id
            for block in ast.walk(node) if isinstance(block, ast.Try)
            for item in block.body
            if isinstance(item, ast.Assign) and len(item.targets) == 1
            and isinstance(item.targets[0], ast.Name)
            and isinstance(item.value, ast.Call)
            and isinstance(item.value.func, ast.Name) and item.value.func.id == "int"
        }

    def _infer(self, node):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id in {"raised", "decimal_valid"} and self.spec_mode:
                return "bool"
        return super()._infer(node)

    def _call(self, node):
        if isinstance(node.func, ast.Name):
            name = node.func.id
            if name == "raised":
                if not self.spec_mode or node.keywords or len(node.args)>1:
                    raise _err(node, "raised() is specification-only and accepts at most one modeled exception name")
                if node.args:
                    value=node.args[0]
                    if not self.tagged or not isinstance(value,ast.Constant) or type(value.value) is not str:
                        raise _err(node,"raised(class) requires a modeled exception name string")
                    return self._matches_error(self.error_name,value.value,node)
                return f"({self.error_name} != 0)" if self.tagged else self.error_name
            if name == "decimal_valid":
                if not self.spec_mode or len(node.args) != 1 or node.keywords or self._infer(node.args[0]) != "string":
                    raise _err(node, "decimal_valid(str) is specification-only")
                return f"PyTryDecimal({self.expr(node.args[0])}).PySome?"
            if name == "int":
                if not self.spec_mode:
                    raise _err(node, "outcome int(str) requires a direct assignment in a supported try block")
                if len(node.args) != 1 or node.keywords or self._infer(node.args[0]) != "string":
                    raise _err(node, "outcome int() requires one str argument")
                return f"PyTryDecimal({self.expr(node.args[0])}).v"
        return super()._call(node)

    def _loop_clauses(self, loop, indent, extra=()):
        super()._loop_clauses(loop, indent, extra + ((f"{self.error_name} == 0" if self.tagged else f"!{self.error_name}"),))

    def _matches_error(self, value, name, node):
        if name not in {"Exception", *self.exception_tags}:raise _err(node,"exception handler needs a modeled class")
        if name == "Exception":return f"{value} != 0"
        tags=[]
        for cls,tag in self.exception_tags.items():
            ancestor=cls
            while True:
                if ancestor==name:
                    tags.append(tag);break
                if ancestor not in self.exceptions:break
                ancestor=self.exceptions[ancestor]
        return "(" + " || ".join(f"{value} == {tag}" for tag in tags) + ")"

    def _emit_error(self, tag, indent):
        if self.handler_target is not None:
            label,pending=self.handler_target
            self.emit(f"{indent}{pending} := {tag}; break {label};")
        else:
            self.emit(f"{indent}{self.error_name} := {tag}; return;")

    def _tagged_try(self, stmt, indent):
        if stmt.finalbody or any(h.name is not None or not isinstance(h.type,ast.Name) for h in stmt.handlers):
            raise _err(stmt,"tagged try supports named exception handlers without bindings or finally")
        for handler in stmt.handlers:self._matches_error("0",handler.type.id,handler)
        pending=self._fresh("pending_error");label=self._fresh("exception_region")
        self.emit(f"{indent}var {pending}: int := 0;")
        self.emit(f"{indent}label {label}: {{")
        outer=self.handler_target
        self.handler_target=(label,pending)
        self.block(stmt.body,indent+"  ")
        self.handler_target=outer
        self.emit(f"{indent}}}")
        self.emit(f"{indent}if {pending} == 0 {{")
        self.block(stmt.orelse,indent+"  ")
        for handler in stmt.handlers:
            self.emit(f"{indent}}} else if {self._matches_error(pending,handler.type.id,handler)} {{")
            self.block(handler.body,indent+"  ")
        self.emit(f"{indent}}} else {{")
        self._emit_error(pending,indent+"  ")
        self.emit(f"{indent}}}")

    def _index_tuple_check(self, stmt, indent):
        """An eager, pure string-index generator raises before tuple assignment.

        The alphabet and source strings are immutable local reads. A missing
        character is exactly the ValueError outcome of materialization; only
        the all-present branch evaluates the partial index function.
        """
        value=stmt.value if isinstance(stmt,(ast.Assign,ast.AnnAssign)) else None
        if not (isinstance(value,ast.Call) and isinstance(value.func,ast.Name) and value.func.id=="tuple"
                and len(value.args)==1 and not value.keywords and isinstance(value.args[0],ast.GeneratorExp)):
            return
        gen=value.args[0]
        if len(gen.generators)!=1:return
        comp=gen.generators[0];elt=gen.elt
        if (comp.is_async or comp.ifs or not isinstance(comp.target,ast.Name)
                or not isinstance(elt,ast.Call) or not isinstance(elt.func,ast.Attribute) or elt.func.attr!="index"
                or not isinstance(elt.func.value,ast.Name) or self._infer(elt.func.value)!="string"
                or len(elt.args)!=1 or elt.keywords or not isinstance(elt.args[0],ast.Name) or elt.args[0].id!=comp.target.id):return
        source=comp.iter
        if isinstance(source,ast.Call) and isinstance(source.func,ast.Name) and source.func.id=="reversed" and len(source.args)==1 and not source.keywords:
            source=source.args[0]
        if isinstance(source,ast.Call) and isinstance(source.func,ast.Name) and source.func.id=="str" and len(source.args)==1 and not source.keywords:
            source=source.args[0]
        if not isinstance(source,ast.Name) or self._infer(source)!="string":return
        binder=self._fresh("index_character")
        alphabet=self.expr(elt.func.value);text=self.expr(source)
        self.emit(f"{indent}if !(forall {binder} :: {binder} in {text} ==> PyStrFind({alphabet}, [{binder}]) >= 0) {{")
        self._emit_error(str(self.exception_tags["ValueError"]),indent+"  ")
        self.emit(f"{indent}}}")

    def stmt(self, stmt, indent):
        if self.tagged:self._index_tuple_check(stmt,indent)
        for clause in self._proofs_by_stmt.pop(id(stmt), []):
            self._emit_proof(clause, indent)
        if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
            value = stmt.value
            if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
                    and value.func.id == "int" and len(value.args) == 1
                    and not value.keywords and self._infer(value.args[0]) == "string"):
                target = stmt.target if isinstance(stmt, ast.AnnAssign) else stmt.targets[0]
                if isinstance(stmt, ast.Assign) and len(stmt.targets) != 1:
                    raise _err(stmt, "decimal conversion requires one assignment target")
                if not (isinstance(target, ast.Name) or isinstance(target, ast.Subscript)
                        and isinstance(target.value, ast.Name)
                        and isinstance(target.slice, (ast.Name, ast.Constant))):
                    raise _err(target, "decimal assignment requires a name or a simple list slot")
                if any(isinstance(n, ast.Call) for n in ast.walk(value.args[0])):
                    raise _err(value, "direct decimal assignment requires a call-free string expression")
                # Python evaluates the RHS before looking up the assignment
                # target. Commit the target only after conversion succeeds.
                converted = self._fresh("direct_decimal")
                self.emit(f"{indent}var {converted} := PyTryDecimal({self.expr(value.args[0])});", stmt.lineno)
                self.emit(f"{indent}if {converted}.PyNone? {{")
                if self.tagged:
                    self._emit_error(str(self.exception_tags["ValueError"]), indent + "  ")
                else:
                    self.emit(f"{indent}  {self.error_name} := true; return;")
                self.emit(f"{indent}}}")
                scalar = self._fresh("decimal_value")
                self.emit(f"{indent}var {scalar}: int := {converted}.v;")
                self.types[scalar] = "int"
                replacement = copy.copy(stmt)
                replacement.value = ast.copy_location(ast.Name(id=scalar, ctx=ast.Load()), value)
                return super().stmt(replacement, indent)
        if isinstance(stmt, ast.Return) and self.none_return:
            if stmt.value is not None and not (isinstance(stmt.value, ast.Constant) and stmt.value.value is None):
                raise _err(stmt, "None outcome methods can only return None")
            self.emit(f"{indent}return;", stmt.lineno)
            return
        if isinstance(stmt, ast.Raise):
            for clause in self._proofs_by_stmt.pop(id(stmt), []):
                self._emit_proof(clause, indent)
            exc = stmt.exc
            if not (isinstance(exc, ast.Call) and isinstance(exc.func, ast.Name)
                    and exc.func.id in {"ValueError", *self.exceptions} and (len(exc.args) == 1 or self.tagged and len(exc.args) == 0) and not exc.keywords
                    and (stmt.cause is None or isinstance(stmt.cause, ast.Constant) and stmt.cause.value is None)):
                raise _err(stmt, "Only raise ValueError(pure string), optionally from None, is modeled")
            message = exc.args[0] if exc.args else ast.Constant(value="")
            if isinstance(message, ast.BinOp) and isinstance(message.op, ast.Mod):
                from veripy.frontend.exception_format import percent_char_operand
                try: operand = percent_char_operand(message)
                except ValueError as exc: raise _err(message, str(exc)) from exc
                if self._infer(operand) != "string":
                    raise _err(operand, "exception %c operand requires a builtin string")
                temporary = self._fresh("format_character")
                self.emit(f"{indent}var {temporary} := {self.expr(operand)};", stmt.lineno)
                # TypeError is outside this backend's ValueError outcome set.
                # Prove formatting succeeds; do not erase its possible failure.
                self.emit(f"{indent}assert |{temporary}| == 1;", stmt.lineno)
            elif isinstance(message, ast.JoinedStr):
                for part in message.values:
                    if isinstance(part, ast.Constant) and type(part.value) is str:
                        continue
                    if (isinstance(part, ast.FormattedValue) and part.conversion in (-1, 114)
                            and part.format_spec is None and isinstance(part.value, ast.Name)
                            and self._infer(part.value) == "string"):
                        continue
                    if (isinstance(part, ast.FormattedValue) and part.conversion == -1
                            and part.format_spec is None and isinstance(part.value, (ast.Name, ast.Subscript))
                            and (self._infer(part.value) == "int" or self._infer(part.value) in self.record_fields)):
                        # Evaluate indexing well-formedness before the modeled raise.
                        self.emit(f"{indent}var {self._fresh('message_value')} := {self.expr(part.value)};", stmt.lineno)
                        continue
                    if (isinstance(part, ast.FormattedValue) and part.conversion == 114
                            and part.format_spec is None and isinstance(part.value, ast.Call)
                            and isinstance(part.value.func, ast.Name) and part.value.func.id == "list"
                            and len(part.value.args) == 1 and not part.value.keywords
                            and isinstance(part.value.args[0], ast.Name)
                            and self._infer(part.value.args[0]) == "seq<int>"):
                        # Exact builtin list[int] copy/repr has no modeled exception.
                        # list binding is excluded at every scope by the module gate below.
                        self.emit(f"{indent}var {self._fresh('message_values')} := {self.expr(part.value.args[0])};", stmt.lineno)
                        continue
                    raise _err(message, "Exception messages allow literal text and pure scalar/record fields")
            elif not isinstance(message, ast.Constant) or type(message.value) is not str:
                raise _err(message, "Exception message must be literal text or a supported str f-string")
            if self.tagged:self._emit_error(str(self.exception_tags[exc.func.id]),indent)
            else:
                self.emit(f"{indent}{self.error_name} := true;", stmt.lineno)
                self.emit(f"{indent}return;")
            return
        if isinstance(stmt, ast.Try):
            if self.tagged:
                self._tagged_try(stmt,indent);return
            if (stmt.finalbody or len(stmt.handlers) != 1 or stmt.handlers[0].name is not None
                    or not isinstance(stmt.handlers[0].type, ast.Name)
                    or stmt.handlers[0].type.id != "ValueError"
                    or len(stmt.handlers[0].body) != 1
                    or not isinstance(stmt.handlers[0].body[0], ast.Raise)):
                raise _err(stmt, "Outcome try supports one ValueError handler that raises, and optional else")
            assignments = []
            for item in stmt.body:
                if not (isinstance(item, ast.Assign) and len(item.targets) == 1
                        and isinstance(item.targets[0], ast.Name) and isinstance(item.value, ast.Call)
                        and isinstance(item.value.func, ast.Name) and item.value.func.id == "int"
                        and len(item.value.args) == 1 and not item.value.keywords
                        and self._infer(item.value.args[0]) == "string"):
                    raise _err(item, "try body must contain direct int(str) assignments")
                name = item.targets[0].id
                if name in self.params or self._declared(name) or name in self.hoisted:
                    raise _err(item, "Outcome conversion targets must be fresh local names")
                assignments.append(item)
                self.types[name] = "int"
                self._declare(name)
                self.emit(f"{indent}var {self._mangle(name)}: int := 0;", item.lineno)
            pending = self._fresh("conversion_failed")
            label = self._fresh("conversion_try")
            self.emit(f"{indent}var {pending} := false;")
            self.emit(f"{indent}label {label}: {{")
            for item in assignments:
                temp = self._fresh("converted")
                self.emit(f"{indent}  var {temp} := PyTryDecimal({self.expr(item.value.args[0])});", item.lineno)
                self.emit(f"{indent}  if {temp}.PyNone? {{ {pending} := true; break {label}; }}")
                self.emit(f"{indent}  {self._mangle(item.targets[0].id)} := {temp}.v;")
            self.emit(f"{indent}}}")
            self.emit(f"{indent}if {pending} {{")
            self.block(stmt.handlers[0].body, indent + "  ")
            self.emit(f"{indent}}} else {{")
            self.block(stmt.orelse, indent + "  ")
            self.emit(f"{indent}}}")
            return
        return super().stmt(stmt, indent)

    def encode(self):
        node = self.node
        args = node.args
        _checked_defaults(node)
        for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs):
            self.types[arg.arg] = _dafny_type(arg.annotation, arg, self.records)
        self.none_return = isinstance(node.returns, ast.Constant) and node.returns.value is None
        self.return_type = "bool" if self.none_return else _dafny_type(node.returns, node, self.records)
        if not self.none_return and not (self.return_type.startswith("seq<") or self.return_type in {"int", "bool", "string"}):
            raise _err(node, "Outcome methods require a scalar, list or None return type")
        if self.none_return and any(isinstance(n, ast.Name) and n.id == "result"
                for clause in self.spec.clauses for n in ast.walk(ast.parse(clause.desugared, mode="eval"))):
            raise _err(node, "None outcome contracts use raised(); result is not exposed")
        self.error_name = self._fresh("outcome_error")
        self.hoisted = self._hoist_analysis()
        params = ", ".join(f"{self._mangle(a.arg)}: {self.types[a.arg]}"
                           for a in (*args.posonlyargs, *args.args, *args.kwonlyargs))
        # Separate exact-contract VCs from nonlinear loop arithmetic. This is
        # verification scheduling only; every obligation is still checked.
        isolate = "{:isolate_assertions} " if self.spec.by_kind("ghost_ensures") else ""
        self.emit(f"method {isolate}{self._mangle(node.name)}({params}) returns (result: {self.return_type}, {self.error_name}: {'int' if self.tagged else 'bool'})", node.lineno)
        for kind in ("requires", "ensures"):
            for clause in self.spec.by_kind(kind):
                self.emit(f"  {kind} {self.spec_expr(clause)}", clause.line)
        for clause in self.spec.by_kind("ghost_ensures"):
            self.emit(f"  ensures {self.spec_expr(clause)}", clause.line)
        self.emit("{")
        initial = {"bool": "false", "int": "0", "string": '\"\"'}.get(self.return_type, "[]")
        self.emit(f"  result := {initial}; {self.error_name} := {'0' if self.tagged else 'false'};")
        for name, dtype in self.hoisted.items():
            self.emit(f"  var {self._mangle(name)}: {dtype};", node.lineno)
            self.types.setdefault(name, dtype)
        self.block(node.body, "  ")
        self.emit("}")


def encode_outcomes(source, specs, module_name="module.py", proof_lemmas=frozenset()):
    if specs.errors:
        first = specs.errors[0]
        raise EncodeError(f"spec error: {first.error}", first.line)
    module = ast.parse(source)
    _module_shadow_check(module)
    from veripy.backends.dafny.environment import resolve_for_encoder, EnvironmentError
    try:
        environment = resolve_for_encoder(module)
    except EnvironmentError as exc:
        raise EncodeError(exc.message, exc.line, "module-environment") from exc
    module = environment.module
    from veripy.frontend.fixed_loops import lower_fixed_loops
    module = lower_fixed_loops(module, specs)
    try:
        records = record_schemas(module)
    except RecordError as exc:
        raise EncodeError(str(exc), exc.line) from exc
    functions = [n for n in module.body if isinstance(n, ast.FunctionDef)]
    by_key = {(n.name, n.lineno): n for n in functions}
    if (not functions or len(functions) != len(specs.functions)
            or len({n.name for n in functions}) != len(functions)
            or any((sp.name, sp.lineno) not in by_key for sp in specs.functions)):
        raise EncodeError("Outcome modules require every top-level function to be uniquely specified", None)
    for node in module.body:
        if not (isinstance(node, ast.FunctionDef) or isinstance(node, ast.ImportFrom) and node.module=="werkzeug" and any(m["kind"]=="etag" for m in environment.regex_models.values())
                or isinstance(node, ast.ImportFrom)
                and node.module in {"__future__", "typing", "dataclasses", "math", "bisect"}
                or isinstance(node, ast.Import) and all(a.name in ({"math", "sys", "re"} if environment.regex_models else {"math", "sys"}) and not a.asname for a in node.names)
                or isinstance(node, ast.ClassDef) and node.name in records):
            raise _err(node, "Outcome modules allow only specified functions and supported imports/records")
    reserved = {"raised", "decimal_valid", "ValueError", *environment.exceptions}
    if environment.exceptions:reserved.add("Exception")
    for n in ast.walk(module):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store) and n.id in reserved:
            raise _err(n, "Outcome intrinsic/exception name is reserved")
        if isinstance(n, (ast.arg, ast.FunctionDef)) and (n.arg if isinstance(n, ast.arg) else n.name) in reserved:
            raise _err(n, "Outcome intrinsic/exception name is reserved")
    for node in module.body:
        if isinstance(node, ast.ImportFrom):
            if node.module=="werkzeug" and any(m["kind"]=="etag" for m in environment.regex_models.values()):continue
            allowed = {"__future__": {"annotations"}, "typing": {"Optional", "Tuple", "NewType", "cast"},
                       "dataclasses": {"dataclass"}, "math": {"prod"},
                       "bisect": {"bisect_right", "insort"}}
            # A source-preserving closure can retain collateral typing imports.
            # Union is harmless only when unused. This does not admit Union
            # annotations or runtime typing operations, including quoted types.
            if node.module == "typing" and not any(
                isinstance(n, ast.Name) and n.id == "Union" or
                isinstance(n, ast.Constant) and isinstance(n.value, str) and "Union" in n.value
                for n in ast.walk(ast.parse(source))
            ):
                allowed["typing"].add("Union")
            if node.level or any(a.asname or a.name not in allowed[node.module] for a in node.names):
                raise _err(node, "Outcome imports permit only supported unaliased names")
    math_names, math_aliases, math_other = _collect_math_imports(module)
    for binding in ast.walk(module):
        name = (binding.arg if isinstance(binding, ast.arg) else
                binding.id if isinstance(binding, ast.Name) and isinstance(binding.ctx, (ast.Store, ast.Del)) else
                binding.name if isinstance(binding, (ast.FunctionDef, ast.ClassDef)) else
                (binding.asname or binding.name).split(".")[0] if isinstance(binding, ast.alias) else None)
        if name == "list":
            raise _err(binding, "binding shadows list used by the outcome fragment")
    sequence_imports = _sequence_imports(module)
    helpers = _helper_signatures(module, specs, records)
    if environment.exceptions:helpers = {name:replace(sig,outcome=True) for name,sig in helpers.items()}
    reserved_names = frozenset(
        n.id if isinstance(n, ast.Name) else n.arg if isinstance(n, ast.arg) else n.name
        for n in ast.walk(module) if isinstance(n, (ast.Name, ast.arg, ast.FunctionDef)))
    encoders = []
    for spec in specs.functions:
        fn = by_key[(spec.name, spec.lineno)]
        if fn.decorator_list or getattr(fn, "type_params", ()):
            raise _err(fn, "Outcome functions do not support decorators or type parameters")
        # Helpers have ordinary returns. Entry points expose ValueError as an
        # additional modeled outcome; calls to outcome entry points stay rejected.
        outcome = (bool(environment.exceptions) or len(functions) == 1
                   or any("raised(" in (c.desugared or c.raw) for c in spec.clauses)
                   or isinstance(fn.returns, ast.Constant) and fn.returns.value is None
                   or any(isinstance(n, (ast.Raise, ast.Try)) for n in ast.walk(fn)))
        none_return = isinstance(fn.returns, ast.Constant) and fn.returns.value is None
        if outcome and not environment.exceptions and not none_return and (not isinstance(fn.body[-1], (ast.Return, ast.Raise)) or any(
                isinstance(n, ast.Return) and n.value is None for n in ast.walk(fn))):
            raise _err(fn, "Outcome functions require an explicit final return or raise, and no bare returns")
        if outcome and fn.name in helpers and not environment.exceptions:
            raise _err(fn, "Calls to outcome functions are outside checked composition")
        cls = OutcomeEncoder if outcome else _MethodEncoder
        if not outcome:
            from veripy.backends.dafny.encoder import _localize_scalar_parameters
            fn,spec=_localize_scalar_parameters(fn,spec,reserved_names)
        encoders.append(cls(fn, spec, proof_lemmas, source_lines=source.split("\n"),
                           records=records, math_names=math_names, math_aliases=math_aliases,
                           math_other=math_other, sequence_imports=sequence_imports,
                           helpers=helpers, reserved_names=reserved_names, module_values=environment.values, regex_models=environment.regex_models, newtypes=environment.newtypes, casts=environment.casts, exceptions=environment.exceptions))
    if helpers:
        all_names = set().union(*(enc.used_names for enc in encoders))
        for enc in encoders:
            enc.used_names.update(all_names)
            enc.mangle_map = enc._build_mangle_map()
    lines = [f"// Generated outcome model from {module_name}", *PREAMBLE.splitlines(), *decimal.preamble().splitlines(),
             *(unicode_strings.preamble().splitlines() if unicode_strings.needed(module) or environment.regex_models else []),
             *(regex_strings.PREAMBLE.splitlines() if environment.regex_models else [])]
    for name, fields in records.items():
        args = ", ".join(f"{record_field(f)}: {_dafny_type(t, t, records)}" for f, t in fields)
        lines.append(f"datatype {record_type(name)} = {record_constructor(name)}({args})")
    line_map, method_names = {}, {}
    for enc in encoders:
        enc.encode()
        offset = len(lines)
        lines.extend(enc.lines)
        lines.append("")
        line_map.update({offset+i+1: line for i,line in enc.line_map.items()})
        method_names[enc.node.name] = enc._mangle(enc.node.name)
        for _, declaration, py_line in enc.quantified_functions.values():
            for declaration_line in declaration:
                lines.append(declaration_line)
                line_map[len(lines)] = py_line
            lines.append("")
    lines.append("// ---- STUB END: proof additions go below ----")
    return EncodedModule("\n".join(lines)+"\n", line_map, list(method_names), method_names)


class OutcomeBackend(DafnyBackend):
    name = "dafny-outcomes"

    @property
    def preamble_version(self):
        return decimal.version()

    def encode(self, source, specs, *, module_name, proof_lemmas):
        return encode_outcomes(source, specs, module_name, proof_lemmas)


register_backend("dafny-outcomes", OutcomeBackend)
