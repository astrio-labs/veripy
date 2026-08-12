"""Read-only fragment conformance survey (M0 prototype).

This is NOT the M1 conformance checker. It runs without type information
(basedpyright integration pending) and approximates the allowlist rules of
ARCHITECTURE.md §3.1 at the AST level. Its M0 job is telemetry (RQ1 in
EVALUATION.md): what fraction of real typed functions falls inside the
candidate fragment, and which rules fire most — the fire counts rank what
v1.5 should admit next.

Fire unit: one fire per construct occurrence (per decorator, per call, per
literal), so rule counts are comparable across rules. Star imports and
module-level escape hatches are file-level fires, counted once and not
attributed to functions.

Known approximations, deliberate for M0:
- No type info: method calls are judged optimistically by *name* against the
  modeled container/str method surface; heterogeneous `==`, `Any` leaks, and
  subclass tricks are invisible until basedpyright integration.
- Functions are the unit of measurement; module-level statements are not
  scored (module-level escape hatches surface as file-level fires only).
- A nested function is scored twice: once as an exclusion fire on its parent
  (`X-NESTED`), once as a function in its own right.
- Comprehension targets are treated as local names although Python gives them
  their own scope; bitwise integer operators are treated as in-fragment;
  decorator argument expressions are not walked (the decorator itself already
  fires `X-DECOR`).
"""

from __future__ import annotations

import ast
import io
import tokenize
from dataclasses import dataclass, field
from pathlib import Path

from .parse import SAFE_BUILTINS

# --------------------------------------------------------------------------
# Rules. `ref` points at the design source: ARCHITECTURE.md section or
# lowering-catalog bucket. Prefix = bucket: F forbidden dynamism, T semantic
# trap, X excluded construct (v1), U unmodeled surface.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Rule:
    id: str
    title: str
    ref: str


_RULES = [
    Rule("F-EVAL", "eval/exec/compile (called, referenced, or rebound)", "§3.1 reflection"),
    Rule("F-REFL", "getattr/setattr/delattr/hasattr/globals/locals/vars", "§3.1 reflection"),
    Rule("F-DUNDER-ATTR", "dunder attribute access (__dict__, __class__, ...)", "§3.1 reflection"),
    Rule("F-DYNIMPORT", "importlib/ctypes/sys.modules/__import__", "§3.1 reflection"),
    Rule("F-CAST", "typing.cast (any spelling or alias)", "§3.1 escape hatches"),
    Rule("F-IGNORE", "# type: ignore / # pyright: ignore", "§3.1 escape hatches"),
    Rule("F-METACLASS", "non-default metaclass", "§3.1 reflection"),
    Rule("T-FLOAT", "float literal, float() call, or float annotation", "§7.2"),
    Rule("T-DIV", "true division `/` (returns float; fixit: //)", "§7.1"),
    Rule("T-IS", "`is` against something other than None/True/False", "§3.1 semantic traps"),
    Rule("T-MUT-DEFAULT", "mutable default argument", "§3.1 semantic traps"),
    Rule("T-GLOBAL", "write access to module-level state", "§3.1 semantic traps"),
    Rule("T-FSTRING", "f-string / string interpolation", "§7 curated-str candidate"),
    Rule("X-TRY", "try/except/finally", "§7.4"),
    Rule("X-RAISE", "raise", "§7.4"),
    Rule("X-WITH", "with statement", "§7 excluded"),
    Rule("X-YIELD", "yield / generator function", "§7.5"),
    Rule("X-ASYNC", "async function", "§7 excluded"),
    Rule("X-DECOR", "function decorator (one fire per decorator)", "§7 excluded (function surgery)"),
    Rule("X-NESTED", "nested function/class definition", "§7.6"),
    Rule("X-CLASS-INHERIT", "method of a class with bases", "§7 excluded (inheritance)"),
    Rule("X-CLASS-DECOR", "method of a class with a non-dataclass decorator", "§7 excluded"),
    Rule("X-DUNDER-DEF", "user-defined dunder method", "§3.1 sealing"),
    Rule("X-VARARG", "*args/**kwargs in signature (one fire each)", "fragment signature rules"),
    Rule("X-STARCALL", "*/** unpacking at a call site", "§7 excluded"),
    Rule("X-DELETE", "del statement", "§7 excluded"),
    Rule("X-ASSERT", "assert statement", "candidate (maps to VC)"),
    Rule("X-ATTR-STORE", "attribute assignment (any binding construct)", "§3.1 attributes"),
    Rule("X-LOOP-ELSE", "for/while else clause", "§7 excluded"),
    Rule("X-WALRUS", "walrus assignment expression", "candidate"),
    Rule("U-OP", "operator without a catalog row (**, @)", "§7 catalog"),
    Rule("U-CONST", "literal type without a catalog row (bytes, complex, ...)", "§7 catalog"),
    Rule("U-METHOD", "method call outside the modeled container/str surface", "§3.3 Tier 2"),
    Rule("U-CALL", "call to a name outside params/locals/module/builtins", "§3.1 builtin surface"),
    Rule("U-IMPORT-STAR", "from x import * (file-level fire)", "§3.1 imports"),
]

RULES: dict[str, Rule] = {r.id: r for r in _RULES}

# Container/str/dict methods with a (planned) Tier 2 model — judged by name
# only in M0 (no receiver types yet). Deliberately optimistic.
MODELED_METHODS = frozenset({
    # list
    "append", "extend", "insert", "pop", "remove", "index", "count", "copy",
    "sort", "reverse", "clear",
    # dict
    "keys", "values", "items", "get", "setdefault", "update",
    # set
    "add", "discard", "union", "intersection", "difference", "issubset",
    "issuperset",
    # str
    "split", "rsplit", "join", "strip", "lstrip", "rstrip", "find", "rfind",
    "startswith", "endswith", "replace", "lower", "upper", "isdigit",
    "isalpha", "isalnum", "isspace", "splitlines", "format_map", "zfill",
    "ljust", "rjust", "partition", "rpartition", "removeprefix",
    "removesuffix",
})

# Modeled methods that mutate their receiver — used for the global-write trap.
MUTATING_METHODS = frozenset({
    "append", "extend", "insert", "pop", "remove", "sort", "reverse", "clear",
    "add", "discard", "update", "setdefault",
})

_REFLECTION_CALLS = frozenset({"eval", "exec", "compile"})
_REFLECTION_INTROSPECT = frozenset({
    "getattr", "setattr", "delattr", "hasattr", "globals", "locals", "vars",
})
_FORBIDDEN_MODULES = frozenset({"importlib", "ctypes"})
_OK_CONST_TYPES = (bool, int, str, type(None))
_DATACLASS_DECORATOR_NAMES = frozenset({"dataclass", "dataclasses.dataclass"})


@dataclass
class Fire:
    rule: str
    line: int
    detail: str = ""


@dataclass
class FunctionReport:
    qualname: str
    lineno: int
    end_lineno: int
    fires: list[Fire] = field(default_factory=list)

    @property
    def accepted(self) -> bool:
        return not self.fires

    @property
    def loc(self) -> int:
        return self.end_lineno - self.lineno + 1


@dataclass
class FileReport:
    path: str
    functions: list[FunctionReport] = field(default_factory=list)
    file_fires: list[Fire] = field(default_factory=list)
    error: str | None = None


@dataclass(frozen=True)
class ModuleScope:
    """Module-level name environment, collected through module-level control
    flow (a def under `if TYPE_CHECKING:` still binds a module name) but never
    inside function bodies."""
    names: frozenset[str]
    # local binding name -> rule id, for from-imports of forbidden targets
    # (e.g. `from typing import cast as c` maps "c" -> "F-CAST").
    forbidden: dict[str, str]
    # local name -> imported module root (e.g. `import importlib as il` maps
    # "il" -> "importlib"; plain `import sys` maps "sys" -> "sys").
    module_roots: dict[str, str]


def _collect_module_scope(module: ast.Module) -> tuple[ModuleScope, list[Fire]]:
    names: set[str] = set()
    forbidden: dict[str, str] = {}
    module_roots: dict[str, str] = {}
    file_fires: list[Fire] = []

    def collect(node: ast.AST) -> None:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names.add(child.name)
                continue  # do not descend into local scopes
            if isinstance(child, ast.Assign):
                for target in child.targets:
                    for t in ast.walk(target):
                        if isinstance(t, ast.Name):
                            names.add(t.id)
            elif isinstance(child, ast.AnnAssign) and isinstance(child.target, ast.Name):
                names.add(child.target.id)
            elif isinstance(child, ast.Import):
                for alias in child.names:
                    local = alias.asname or alias.name.split(".")[0]
                    names.add(local)
                    root = alias.name.split(".")[0]
                    module_roots[local] = root
                    if root in _FORBIDDEN_MODULES:
                        forbidden[local] = "F-DYNIMPORT"
            elif isinstance(child, ast.ImportFrom):
                root = (child.module or "").split(".")[0]
                for alias in child.names:
                    if alias.name == "*":
                        file_fires.append(Fire("U-IMPORT-STAR", child.lineno, detail=root))
                        continue
                    local = alias.asname or alias.name
                    names.add(local)
                    if root in _FORBIDDEN_MODULES:
                        forbidden[local] = "F-DYNIMPORT"
                    elif root == "typing" and alias.name == "cast":
                        forbidden[local] = "F-CAST"
                    elif alias.name == "__import__":
                        forbidden[local] = "F-DYNIMPORT"
                    elif root == "builtins" and alias.name in _REFLECTION_CALLS:
                        forbidden[local] = "F-EVAL"
                    elif root == "builtins" and alias.name in _REFLECTION_INTROSPECT:
                        forbidden[local] = "F-REFL"
            collect(child)

    collect(module)
    return ModuleScope(frozenset(names), forbidden, module_roots), file_fires


def _ignore_comment_lines(source: str) -> set[int]:
    lines: set[int] = set()
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            if tok.type == tokenize.COMMENT:
                text = tok.string.replace(" ", "")
                if text.startswith("#type:ignore") or text.startswith("#pyright:ignore"):
                    lines.add(tok.start[0])
    except tokenize.TokenError:
        pass
    return lines


def _is_mutable_literal(node: ast.expr) -> bool:
    return isinstance(node, (ast.List, ast.Dict, ast.Set, ast.ListComp,
                             ast.DictComp, ast.SetComp)) or (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"list", "dict", "set", "bytearray"}
    )


def _decorator_name(dec: ast.expr) -> str:
    d = dec
    while isinstance(d, ast.Call):
        d = d.func
    try:
        return ast.unparse(d)
    except Exception:
        return "?"


def _class_flags(node: ast.ClassDef) -> list[tuple[str, str]]:
    """Rules a class definition imposes on every method it contains."""
    flags: list[tuple[str, str]] = []
    if node.bases:
        flags.append(("X-CLASS-INHERIT", node.name))
    if node.keywords:
        flags.append(("F-METACLASS", node.name))
    for dec in node.decorator_list:
        name = _decorator_name(dec)
        if name not in _DATACLASS_DECORATOR_NAMES:
            flags.append(("X-CLASS-DECOR", f"{node.name}: @{name}"))
    return flags


class _FunctionScanner:
    """Scan one function (excluding nested defs) for rule fires."""

    def __init__(
        self,
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        qualname: str,
        scope: ModuleScope,
        class_flags: list[tuple[str, str]],
    ) -> None:
        self.node = node
        self.report = FunctionReport(
            qualname=qualname,
            lineno=node.lineno,
            end_lineno=node.end_lineno or node.lineno,
        )
        self.scope = scope
        self.class_flags = class_flags
        self.local_names = self._local_names()

    def fire(self, rule: str, node: ast.AST, detail: str = "") -> None:
        self.report.fires.append(
            Fire(rule=rule, line=getattr(node, "lineno", self.node.lineno), detail=detail)
        )

    # -- local name environment (approximate; no types) --------------------

    def _local_names(self) -> set[str]:
        """Names bound in *this* function's scope. Traversal stops at nested
        def/class/lambda boundaries (their internals are not our locals; the
        binding's own name is)."""
        names: set[str] = set()
        a = self.node.args
        names.update(p.arg for p in (*a.posonlyargs, *a.args, *a.kwonlyargs))
        if a.vararg:
            names.add(a.vararg.arg)
        if a.kwarg:
            names.add(a.kwarg.arg)

        def walk(node: ast.AST) -> None:
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    names.add(child.name)
                    continue
                if isinstance(child, ast.Lambda):
                    continue
                if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Store):
                    names.add(child.id)
                elif isinstance(child, ast.comprehension):
                    for t in ast.walk(child.target):
                        if isinstance(t, ast.Name):
                            names.add(t.id)
                walk(child)

        for stmt in self.node.body:
            walk(stmt)
            if isinstance(stmt, ast.Name) and isinstance(stmt.ctx, ast.Store):
                names.add(stmt.id)
        return names

    def _is_module_level(self, name: str, locals_: frozenset[str]) -> bool:
        return (
            name in self.scope.names
            and name not in self.local_names
            and name not in locals_
        )

    # -- signature / definition-level rules --------------------------------

    def _scan_signature(self) -> None:
        node = self.node
        if isinstance(node, ast.AsyncFunctionDef):
            self.fire("X-ASYNC", node)
        for dec in node.decorator_list:
            self.fire("X-DECOR", dec, detail=_decorator_name(dec))
        a = node.args
        if a.vararg:
            self.fire("X-VARARG", node, detail=f"*{a.vararg.arg}")
        if a.kwarg:
            self.fire("X-VARARG", node, detail=f"**{a.kwarg.arg}")
        for default in [*a.defaults, *a.kw_defaults]:
            if default is not None:
                if _is_mutable_literal(default):
                    self.fire("T-MUT-DEFAULT", default)
                self._scan_expr_tree(default)
        for arg in (*a.posonlyargs, *a.args, *a.kwonlyargs, a.vararg, a.kwarg):
            if arg is not None and arg.annotation is not None:
                self._scan_expr_tree(arg.annotation)
        if node.returns is not None:
            self._scan_expr_tree(node.returns)
        for rule, detail in self.class_flags:
            self.fire(rule, node, detail=detail)
        if node.name.startswith("__") and node.name.endswith("__") and node.name != "__init__":
            self.fire("X-DUNDER-DEF", node, detail=node.name)

    # -- body walk ----------------------------------------------------------

    def scan(self) -> FunctionReport:
        self._scan_signature()
        for stmt in self.node.body:
            self._scan_stmt(stmt)
        return self.report

    def _scan_stmt(self, stmt: ast.stmt) -> None:
        # Nested defs: fire once, do not descend (they get their own report).
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self.fire("X-NESTED", stmt, detail=stmt.name)
            return
        if isinstance(stmt, ast.ClassDef):
            self.fire("X-NESTED", stmt, detail=f"class {stmt.name}")
            return

        match stmt:
            case ast.Try():
                self.fire("X-TRY", stmt)
            case ast.Raise():
                self.fire("X-RAISE", stmt)
            case ast.With() | ast.AsyncWith():
                self.fire("X-WITH", stmt)
            case ast.Delete():
                self.fire("X-DELETE", stmt)
            case ast.Assert():
                self.fire("X-ASSERT", stmt)
            case ast.Global() | ast.Nonlocal():
                self.fire("T-GLOBAL", stmt)
            case ast.For(orelse=orelse) | ast.While(orelse=orelse) if orelse:
                self.fire("X-LOOP-ELSE", stmt)
            case ast.AugAssign(op=op):
                if isinstance(op, ast.Div):
                    self.fire("T-DIV", stmt)
                elif isinstance(op, (ast.Pow, ast.MatMult)):
                    self.fire("U-OP", stmt, detail=type(op).__name__)
            case _:
                pass

        self._scan_children(stmt)

    def _scan_children(self, node: ast.AST) -> None:
        """Dispatch child nodes: statements recurse through _scan_stmt (which
        also intercepts nested defs), expressions through the expr walker, and
        structural nodes (ExceptHandler, match_case, withitem, ...) recurse
        here so the statements inside them are not missed."""
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.stmt):
                self._scan_stmt(child)
            elif isinstance(child, ast.expr):
                self._scan_expr_tree(child)
            else:
                self._scan_children(child)

    def _scan_expr_tree(self, root: ast.AST, locals_: frozenset[str] = frozenset()) -> None:
        # Collect this scope's nodes without descending into lambda bodies —
        # a lambda's parameters are locals of the lambda, not of us, so its
        # body is scanned recursively with those parameters in scope.
        nodes: list[ast.AST] = []
        lambdas: list[ast.Lambda] = []
        stack: list[ast.AST] = [root]
        while stack:
            current = stack.pop()
            if isinstance(current, ast.Lambda):
                lambdas.append(current)
                continue
            nodes.append(current)
            stack.extend(ast.iter_child_nodes(current))

        call_func_ids = {id(n.func) for n in nodes if isinstance(n, ast.Call)}
        for node in nodes:
            match node:
                case ast.Constant() as c:
                    if isinstance(c.value, bool):
                        pass
                    elif isinstance(c.value, float):
                        self.fire("T-FLOAT", node, detail=repr(c.value))
                    elif not isinstance(c.value, _OK_CONST_TYPES):
                        self.fire("U-CONST", node, detail=type(c.value).__name__)
                case ast.JoinedStr():
                    self.fire("T-FSTRING", node)
                case ast.Yield() | ast.YieldFrom():
                    self.fire("X-YIELD", node)
                case ast.NamedExpr():
                    self.fire("X-WALRUS", node)
                case ast.BinOp(op=op):
                    if isinstance(op, ast.Div):
                        self.fire("T-DIV", node)
                    elif isinstance(op, (ast.Pow, ast.MatMult)):
                        self.fire("U-OP", node, detail=type(op).__name__)
                case ast.Compare(ops=ops, comparators=comps):
                    for op, comp in zip(ops, comps):
                        if isinstance(op, (ast.Is, ast.IsNot)) and not (
                            isinstance(comp, ast.Constant)
                            and (comp.value is None or comp.value is True or comp.value is False)
                        ):
                            self.fire("T-IS", node)
                case ast.Subscript(value=ast.Name(id=base), ctx=ast.Store()):
                    if self._is_module_level(base, locals_):
                        self.fire("T-GLOBAL", node, detail=f"{base}[...] = ...")
                case ast.Attribute() as attr_node:
                    self._scan_attribute(attr_node, locals_)
                case ast.Name(ctx=ast.Load()) as name_node if id(name_node) not in call_func_ids:
                    self._scan_name_load(name_node, locals_)
                case ast.Call() as call_node:
                    self._scan_call(call_node, locals_)
                case _:
                    pass

        for lam in lambdas:
            for default in [*lam.args.defaults, *lam.args.kw_defaults]:
                if default is not None:
                    self._scan_expr_tree(default, locals_)  # defaults evaluate in our scope
            params = frozenset(
                a.arg for a in (*lam.args.posonlyargs, *lam.args.args, *lam.args.kwonlyargs)
            )
            if lam.args.vararg:
                params |= {lam.args.vararg.arg}
            if lam.args.kwarg:
                params |= {lam.args.kwarg.arg}
            self._scan_expr_tree(lam.body, locals_ | params)

    def _scan_attribute(self, node: ast.Attribute, locals_: frozenset[str]) -> None:
        attr = node.attr
        if attr.startswith("__") and attr.endswith("__"):
            self.fire("F-DUNDER-ATTR", node, detail=attr)
        base = node.value
        if isinstance(base, ast.Name):
            shadowed = base.id in self.local_names or base.id in locals_
            root = self.scope.module_roots.get(base.id, base.id if not shadowed else "")
            if root == "sys" and attr == "modules":
                self.fire("F-DYNIMPORT", node, detail="sys.modules")
            elif root in _FORBIDDEN_MODULES:
                self.fire("F-DYNIMPORT", node, detail=f"{root}.{attr}")
            elif root == "typing" and attr == "cast":
                self.fire("F-CAST", node)
            elif root == "builtins" and attr in _REFLECTION_CALLS:
                self.fire("F-EVAL", node, detail=f"builtins.{attr}")
            elif root == "builtins" and attr in _REFLECTION_INTROSPECT:
                self.fire("F-REFL", node, detail=f"builtins.{attr}")
            elif root == "builtins" and attr == "float":
                self.fire("T-FLOAT", node, detail="builtins.float")
        if isinstance(node.ctx, ast.Store):
            self.fire("X-ATTR-STORE", node, detail=attr)
            if isinstance(base, ast.Name) and self._is_module_level(base.id, locals_):
                self.fire("T-GLOBAL", node, detail=f"{base.id}.{attr} = ...")

    def _scan_name_load(self, node: ast.Name, locals_: frozenset[str]) -> None:
        """Bare references to forbidden callables (rebinding launders them:
        `run = eval; run(s)`)."""
        name = node.id
        if name in self.local_names or name in locals_:
            return
        if name in _REFLECTION_CALLS:
            self.fire("F-EVAL", node, detail=name)
        elif name in _REFLECTION_INTROSPECT:
            self.fire("F-REFL", node, detail=name)
        elif name == "__import__":
            self.fire("F-DYNIMPORT", node)
        elif name == "float":
            self.fire("T-FLOAT", node, detail="float annotation/reference")
        elif name in self.scope.forbidden:
            self.fire(self.scope.forbidden[name], node, detail=name)

    def _scan_call(self, node: ast.Call, locals_: frozenset[str]) -> None:
        if any(isinstance(a, ast.Starred) for a in node.args) or any(
            kw.arg is None for kw in node.keywords
        ):
            self.fire("X-STARCALL", node)

        func = node.func
        if isinstance(func, ast.Name):
            name = func.id
            if name in self.local_names or name in locals_:
                return  # locally bound callables are the local's business
            if name in _REFLECTION_CALLS:
                self.fire("F-EVAL", node, detail=name)
            elif name in _REFLECTION_INTROSPECT:
                self.fire("F-REFL", node, detail=name)
            elif name == "cast":
                self.fire("F-CAST", node)
            elif name == "float":
                self.fire("T-FLOAT", node, detail="float()")
            elif name == "__import__":
                self.fire("F-DYNIMPORT", node)
            elif name in self.scope.forbidden:
                self.fire(self.scope.forbidden[name], node, detail=name)
            elif name not in SAFE_BUILTINS and name not in self.scope.names:
                self.fire("U-CALL", node, detail=name)
        elif isinstance(func, ast.Attribute):
            base = func.value
            root = (
                self.scope.module_roots.get(base.id, base.id)
                if isinstance(base, ast.Name)
                and base.id not in self.local_names
                and base.id not in locals_
                else ""
            )
            base_forbidden = (
                root in _FORBIDDEN_MODULES
                or (root == "sys" and func.attr == "modules")
                or (root == "typing" and func.attr == "cast")
                or (root == "builtins" and (
                    func.attr in _REFLECTION_CALLS
                    or func.attr in _REFLECTION_INTROSPECT
                    or func.attr == "float"
                ))
            )
            # F-DYNIMPORT/F-CAST on the attribute itself is fired by
            # _scan_attribute during the same walk; avoid doubling up here.
            if base_forbidden:
                return
            if (
                func.attr in MUTATING_METHODS
                and isinstance(base, ast.Name)
                and self._is_module_level(base.id, locals_)
            ):
                self.fire("T-GLOBAL", node, detail=f"{base.id}.{func.attr}(...)")
            if func.attr not in MODELED_METHODS:
                self.fire("U-METHOD", node, detail=func.attr)


def survey_source(source: str, path: str = "<string>") -> FileReport:
    report = FileReport(path=path)
    try:
        module = ast.parse(source, filename=path)
    except (SyntaxError, ValueError) as exc:
        report.error = f"parse error: {exc}"
        return report

    scope, file_fires = _collect_module_scope(module)
    report.file_fires.extend(file_fires)

    def visit_body(node: ast.AST, qualprefix: str, class_flags: list[tuple[str, str]]) -> None:
        """Find every def outside function bodies, through any module-level
        control flow (if/try/match/with/loops, including except handlers)."""
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                qualname = f"{qualprefix}{child.name}"
                scanner = _FunctionScanner(child, qualname, scope, class_flags)
                report.functions.append(scanner.scan())
                visit_body(child, f"{qualname}.", [])
            elif isinstance(child, ast.ClassDef):
                visit_body(child, f"{qualprefix}{child.name}.", _class_flags(child))
            elif not isinstance(child, ast.expr):
                visit_body(child, qualprefix, class_flags)

    visit_body(module, "", [])

    # `# type: ignore` comments: one fire, attributed to the innermost
    # containing function; module-level ones become file-level fires.
    for line in sorted(_ignore_comment_lines(source)):
        best: FunctionReport | None = None
        for fn in report.functions:
            if fn.lineno <= line <= fn.end_lineno:
                if best is None or fn.loc < best.loc:
                    best = fn
        if best is not None:
            best.fires.append(Fire("F-IGNORE", line))
        else:
            report.file_fires.append(Fire("F-IGNORE", line))
    return report


def survey_paths(paths: list[Path]) -> list[FileReport]:
    reports: list[FileReport] = []
    seen: set[Path] = set()
    for path in paths:
        if path.is_dir():
            files = sorted(path.rglob("*.py"))
        else:
            files = [path]
        for file in files:
            resolved = file.resolve()
            if resolved in seen:
                continue  # overlapping inputs (dir + file inside it) count once
            seen.add(resolved)
            try:
                source = file.read_text(encoding="utf-8", errors="replace")
            except OSError as exc:
                reports.append(FileReport(path=str(file), error=str(exc)))
                continue
            reports.append(survey_source(source, path=str(file)))
    return reports


def aggregate(reports: list[FileReport]) -> dict:
    functions = [fn for r in reports for fn in r.functions]
    accepted = [fn for fn in functions if fn.accepted]
    rule_counts: dict[str, int] = {}
    for fn in functions:
        for fire in fn.fires:
            rule_counts[fire.rule] = rule_counts.get(fire.rule, 0) + 1
    for r in reports:
        for fire in r.file_fires:
            rule_counts[fire.rule] = rule_counts.get(fire.rule, 0) + 1
    total_loc = sum(fn.loc for fn in functions)
    accepted_loc = sum(fn.loc for fn in accepted)
    return {
        "files": len(reports),
        "file_errors": sum(1 for r in reports if r.error),
        "functions": len(functions),
        "accepted": len(accepted),
        "accepted_pct": round(100 * len(accepted) / len(functions), 1) if functions else 0.0,
        "loc": total_loc,
        "accepted_loc": accepted_loc,
        "accepted_loc_pct": round(100 * accepted_loc / total_loc, 1) if total_loc else 0.0,
        "rule_counts": dict(sorted(rule_counts.items(), key=lambda kv: -kv[1])),
    }
