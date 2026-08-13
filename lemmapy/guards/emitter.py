"""Generate `<stem>_guarded.py`: an island copy plus boundary guards.

The guarded module *contains* the original source verbatim (the island — a
byte-identical, auditable copy of what the conformance checker admitted;
proof status is established separately by `lemmapy verify`), then redefines each
spec'd function as a wrapper that deep-type-checks, copies in, evaluates
executable `#@ requires` (blame: caller), calls the island, and — when
generated with ``check_ensures=True`` — evaluates `#@ ensures` on the
result (blame: callee-or-toolchain).

Because the island is a copy, `mock.patch` on the *original* module cannot
swap out what the guarded module runs (island integrity, §5). Trusted
callers elide guard cost by importing the original module directly.
"""

from __future__ import annotations

import ast
import hashlib

from ..frontend.parse import FunctionSpec, ModuleSpecs, rewrite_old


class GuardGenError(Exception):
    def __init__(self, message: str, line: int | None = None):
        super().__init__(message)
        self.message = message
        self.line = line


def _reject_reserved_names(module: ast.Module) -> None:
    """Every identifier the generator emits is `_lemmapy`-prefixed; no name
    in the source may share that prefix, or a parameter/local/module global
    could capture a generated temporary (the old()-snapshot and island-alias
    collisions both silently substituted caller arguments)."""
    for n in ast.walk(module):
        name = None
        if isinstance(n, ast.Name):
            name = n.id
        elif isinstance(n, ast.arg):
            name = n.arg
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            name = n.name
        elif isinstance(n, ast.alias):
            name = (n.asname or n.name).split(".")[0]
        if name is not None and name.startswith("_lemmapy"):
            raise GuardGenError(
                f"name {name!r} is reserved for generated guard code — rename it",
                getattr(n, "lineno", None),
            )


def _descriptor(ann: ast.expr | None, where: ast.AST) -> tuple:
    """Annotation -> runtime type descriptor. Mirrors the encoder's
    `_dafny_type` admission exactly — anything else is outside the fragment."""
    if ann is None:
        raise GuardGenError(
            "missing type annotation (the fragment requires precise types)",
            getattr(where, "lineno", None),
        )
    match ann:
        case ast.Name(id=("int" | "bool" | "str") as name):
            return (name,)
        case ast.Subscript(value=ast.Name(id="list"), slice=inner):
            return ("list", _descriptor(inner, where))
        case ast.Subscript(value=ast.Name(id="Optional"), slice=inner):
            return ("opt", _descriptor(inner, where))
        case ast.BinOp(left=left, op=ast.BitOr(), right=ast.Constant(value=None)):
            return ("opt", _descriptor(left, where))
        case ast.BinOp(left=ast.Constant(value=None), op=ast.BitOr(), right=right):
            return ("opt", _descriptor(right, where))
        case _:
            raise GuardGenError(
                f"type {ast.unparse(ann)!r} is outside the fragment",
                getattr(where, "lineno", None),
            )


def _signature(fn: ast.FunctionDef) -> tuple[str, str, list[tuple[str, ast.expr | None]]]:
    """Rebuild the wrapper signature. Returns (def-params, call-args,
    [(param, annotation), ...])."""
    a = fn.args
    if a.vararg or a.kwarg:
        raise GuardGenError("*args/**kwargs are outside the fragment", fn.lineno)
    if a.defaults or any(d is not None for d in a.kw_defaults):
        raise GuardGenError("parameter defaults are outside the fragment", fn.lineno)
    params: list[tuple[str, ast.expr | None]] = []
    def_parts: list[str] = []
    call_parts: list[str] = []
    for p in (*a.posonlyargs, *a.args):
        params.append((p.arg, p.annotation))
        def_parts.append(p.arg)
        call_parts.append(p.arg)
    if a.posonlyargs:
        def_parts.insert(len(a.posonlyargs), "/")
    if a.kwonlyargs:
        def_parts.append("*")
        for p in a.kwonlyargs:
            params.append((p.arg, p.annotation))
            def_parts.append(p.arg)
            call_parts.append(f"{p.arg}={p.arg}")
    return ", ".join(def_parts), ", ".join(call_parts), params


def _wrapper(fn: ast.FunctionDef, spec: FunctionSpec, check_ensures: bool) -> list[str]:
    name = spec.name
    if "result" in {p.arg for p in (*fn.args.posonlyargs, *fn.args.args, *fn.args.kwonlyargs)}:
        raise GuardGenError("parameter named 'result' shadows the spec word", fn.lineno)
    def_params, call_args, params = _signature(fn)
    body: list[str] = [f"def {name}({def_params}):"]
    for pname, ann in params:
        desc = _descriptor(ann, fn)
        body.append(
            f"    {pname} = _lemmapy_bound_guard({pname}, {desc!r}, "
            f"function={name!r}, param={pname!r})"
        )
    for clause in spec.by_kind("requires"):
        # A requires whose evaluation itself raises (min([]) etc.) is still
        # a caller-side boundary failure, with blame -- never a bare builtin
        # exception escaping the wrapper.
        body.append("    try:")
        body.append(f"        _lemmapy_ok = bool({clause.desugared})")
        body.append("    except Exception as _lemmapy_exc:")
        body.append(
            f"        raise _lemmapy_bound_pre({name!r}, "
            f"{'requires ' + clause.raw!r} + "
            f"f' raised {{type(_lemmapy_exc).__name__}}: {{_lemmapy_exc}}')"
        )
        body.append("    if not _lemmapy_ok:")
        body.append(
            f"        raise _lemmapy_bound_pre({name!r}, "
            f"{'requires ' + clause.raw!r})"
        )
    ensures = spec.by_kind("ensures") if check_ensures else []
    old_names = sorted({n for c in ensures for n in c.old_names})
    descs = {p: _descriptor(ann, fn) for p, ann in params}
    for n in old_names:
        if n not in descs:
            raise GuardGenError(f"old({n}) does not name a parameter", fn.lineno)
        body.append(f"    _lemmapy_old_{n} = _lemmapy_bound_copy({n}, {descs[n]!r})")
    if ensures and params:
        # The island gets its own copies so post-call ensures evaluation
        # reads the wrapper's pre-call values even if the island mutates
        # its parameters (Dafny ensures reads the input value).
        island_parts = []
        for part in call_args.split(", "):
            p = part.split("=")[0]
            copied = f"_lemmapy_bound_copy({p}, {descs[p]!r})"
            island_parts.append(f"{p}={copied}" if "=" in part else copied)
        body.append(f"    result = _lemmapy_bound_island({', '.join(island_parts)})")
    else:
        body.append(f"    result = _lemmapy_bound_island({call_args})")
    for clause in ensures:
        expr = rewrite_old(clause.desugared, "_lemmapy_old_{name}")
        body.append(f"    if not ({expr}):")
        body.append(
            f"        raise _lemmapy_bound_post({name!r}, "
            f"{'ensures ' + clause.raw!r})"
        )
    body.append("    return result")
    # The factory closes over the island and the helpers at definition
    # time: rebinding the guarded module's attributes afterwards cannot
    # redirect an already-defined wrapper (island integrity, ARCHITECTURE
    # 5). Closure-cell surgery remains under assumption A1.
    lines = [f"_lemmapy_island_{name} = {name}", "", ""]
    lines.append(
        f"def _lemmapy_make_{name}(_lemmapy_bound_island, _lemmapy_bound_guard, "
        f"_lemmapy_bound_copy, _lemmapy_bound_pre, _lemmapy_bound_post):"
    )
    lines.extend("    " + b if b else b for b in body)
    lines.append(f"    return {name}")
    lines.append("")
    lines.append("")
    lines.append(
        f"{name} = _lemmapy_make_{name}(_lemmapy_island_{name}, "
        f"_lemmapy_guard_value, _lemmapy_copy_value, "
        f"_LemmapyPreconditionError, _LemmapyPostconditionError)"
    )
    lines.append("")
    lines.append("")
    return lines


def emit_guarded(
    source: str,
    specs: ModuleSpecs,
    src_name: str,
    check_ensures: bool = False,
) -> str:
    """Emit the guarded sibling module for every spec'd function."""
    module = ast.parse(source)
    # Specs cannot smuggle generated identifiers either: the frontend
    # rejects unknown names in clauses, and the two ways a _lemmapy* name
    # could become KNOWN (a parameter, a module-level binding) are both
    # rejected by _reject_reserved_names.
    _reject_reserved_names(module)
    if "# ---- LEMMAPY ISLAND" in source:
        # A source containing sentinel text could truncate the digest's
        # coverage (the integrity checker requires exactly one of each
        # sentinel; this keeps generation and verification consistent).
        raise GuardGenError("island sentinel text may not appear in the source")
    for n in ast.walk(module):
        if isinstance(n, ast.ImportFrom) and n.level > 0:
            # The guarded sibling lives under the output directory, outside
            # the source's package context — a relative import in the island
            # copy would fail at import time.
            raise GuardGenError(
                "package-relative imports cannot survive relocation into the "
                "guarded sibling module — use absolute imports", n.lineno)
    for stmt in module.body:
        if isinstance(stmt, ast.ImportFrom) and stmt.module == "__future__":
            # The island is a verbatim mid-file copy; a __future__ import
            # there would be a SyntaxError, and silently hoisting it would
            # break the byte-identical-island property.
            raise GuardGenError(
                "__future__ imports are not supported in guarded modules "
                "(fragment types need none)", stmt.lineno)
    # Only module-level functions can be guarded: the island alias binds
    # the name at module scope, which a nested def never reaches (the
    # generated module would import cleanly and NameError on first call).
    fn_nodes = {
        (n.name, n.lineno): n
        for n in module.body
        if isinstance(n, ast.FunctionDef)
    }
    guarded: list[str] = []
    out: list[str] = [
        f'"""Generated by `lemmapy guard` from {src_name} -- DO NOT EDIT.',
        "",
        "The island below is a verbatim copy of the source as admitted by",
        "the conformance checker; its PROOF status is established separately",
        "by `lemmapy verify` (the guards enforce the written spec either",
        "way). Wrappers after it are the boundary (ARCHITECTURE §4). Trusted",
        f"callers import {src_name} directly to elide guard cost.",
        '"""',
        "",
        "from lemmapy.guards.runtime import (",
        "    PostconditionError as _LemmapyPostconditionError,",
        "    PreconditionError as _LemmapyPreconditionError,",
        "    copy_value as _lemmapy_copy_value,",
        "    guard_value as _lemmapy_guard_value,",
        ")",
        "",
        "# ---- LEMMAPY ISLAND BEGIN (verbatim copy of the admitted source) ----",
        source.rstrip("\n"),
        "# ---- LEMMAPY ISLAND END ----",
        "",
        "",
        "# ---- boundary guards (generated) ----",
        "",
        f'_LEMMAPY_ISLAND_SHA256 = "{hashlib.sha256(source.rstrip(chr(10)).encode()).hexdigest()}"',
        "",
        "",
    ]
    for spec in specs.functions:
        node = fn_nodes.get((spec.name, spec.lineno))
        if node is None:
            raise GuardGenError(
                f"cannot guard {spec.name!r}: only module-level functions "
                f"can carry a boundary", spec.lineno)
        if any(c.error for c in spec.clauses):
            raise GuardGenError(
                f"{spec.name}: spec errors — fix them before guarding", spec.lineno
            )
        out.extend(_wrapper(node, spec, check_ensures))
        guarded.append(spec.name)
    if not guarded:
        raise GuardGenError("no spec'd functions to guard")
    out.append(f"__all__ = {guarded!r}")
    out.append("")
    return "\n".join(out)
