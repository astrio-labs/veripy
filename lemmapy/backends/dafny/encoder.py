"""M1 slice-1 encoder: the clean-bucket fragment -> Dafny method stubs.

Scope (deliberately small; everything else is a detected, explained
rejection):
- types: int, bool, str, list[int|str|bool] (reads only: len, indexing —
  including negative indices, normalized Python-exactly via PyIndex)
- statements: assignment (incl. parallel tuple), if/elif/else, while,
  `for i in range(...)` (lowered to while with an auto bounds invariant),
  return
- expressions: arithmetic with PyFloorDiv/PyMod, comparisons (chained),
  and/or/not, len/min/max/abs, indexing, conditional expressions
- specs: requires/ensures/invariant/decreases; forall/exists over range or
  membership domains; `result`; `old(param)` lowers to the parameter (our
  fragment's parameters are immutable — guards copy in, ownership forbids
  parameter mutation)

Soundness rules enforced here (each closes a reviewed miscompilation class):
- Order comparisons (< <= > >=) only between ints (or two indexed chars):
  Dafny's seq `<` is PREFIX order, Python's is lexicographic.
- `in`/`not in` only against list-typed operands: Python's `in` on str is
  SUBSTRING search, Dafny's is element membership.
- `bool(e)` in specs (the `<==>` desugar) requires a bool-typed operand:
  anything else would silently drop Python truthiness.
- The range-for index is RETIRED after its loop: Python leaves it at the
  last iterated value (or unbound), the lowering leaves it at the bound.
- Quantifier binders may not shadow parameters or locals: Python evaluates
  the domain in the enclosing scope, Dafny's binder would capture it.
- Identifier renaming (Dafny keywords -> name_py, hoisted loop bounds) is
  made injective against every identifier appearing in the function.
- Locals assigned across sibling branches are hoisted (`var x: T;`) so
  Dafny's block scoping matches Python's function scoping; Dafny's definite
  assignment then guards use-before-assign.
- `x += y` only on ints: Python's list `+=` mutates aliases in place.
- One definition per function name per module: CPython runs the LAST def,
  the verifier would prove the first.
- `#@ invariant`/`#@ decreases` must sit at the top of the loop body,
  before its first statement (the documented convention, now enforced —
  trailing comment lines would otherwise attach to the wrong loop).

Semantics note baked in here: `#@ invariant` has Dafny loop-head semantics
(holds on entry and at every head check, including the final one where the
guard is false). The range-for lowering auto-supplies the index bounds
invariant; range() bounds are hoisted because Python evaluates them once.

Output is a single self-contained .dfy stub (preamble inlined). The
additions-only proof discipline is enforced diff-wise, LemmaScript-benchmark
style; the two-file stub/proof split from ARCHITECTURE arrives when the
proof loop does.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass
from pathlib import Path

from ...frontend.parse import Clause, FunctionSpec, ModuleSpecs
from .preamble import PREAMBLE


@dataclass(frozen=True)
class ProofSidecar:
    text: str
    lemmas: frozenset[str]

    @staticmethod
    def empty() -> "ProofSidecar":
        return ProofSidecar("", frozenset())


def _strip_dafny_comments(text: str) -> str:
    """Remove // and (nested) /* */ comments AND blank all string/char
    literal interiors — string contents are irrelevant to structural
    validation, and a brace inside a string must never read as declaration
    structure (the `ensures s == "a{"` axiom vector)."""
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        c = text[i]
        if depth == 0 and c == '"':
            # Emit an EMPTY string literal; skip the real contents.
            out.append('""')
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        if depth == 0 and c == "'":
            # A quote directly after an identifier char is a prime
            # (Dafny allows x' names), not a char literal.
            prev = out[-1][-1] if out and out[-1] else ""
            if not (prev.isalnum() or prev in "_'"):
                out.append("'?'")
                i += 1
                while i < n:
                    if text[i] == "\\" and i + 1 < n:
                        i += 2
                        continue
                    if text[i] == "'":
                        i += 1
                        break
                    i += 1
                continue
            out.append(c)
            i += 1
            continue
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            depth += 1
            i += 2
            continue
        if c == "*" and i + 1 < n and text[i + 1] == "/" and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0 and c == "/" and i + 1 < n and text[i + 1] == "/":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if depth == 0:
            out.append(c)
        i += 1
    return "".join(out)


_SIDECAR_FORBIDDEN = frozenset({
    "method", "import", "include", "print", "expect", "assume", "axiom",
    "twostate", "iterator", "class", "trait", "module", "new", "modifies",
    # Collection displays put braces after identifiers (`multiset{1}`), which
    # would let a bodiless lemma masquerade as proved; lemma packs about the
    # fragment's arithmetic don't need them — forbid the whole class.
    "multiset", "set", "iset", "map", "imap",
})
_SIDECAR_DECL_KEYWORDS = frozenset({"lemma", "function", "predicate", "ghost"})
# Words that cannot END a value/signature — a top-level `{` following one of
# these is a brace-delimited literal in specification position, not a body.
_SIDECAR_NON_ENDERS = frozenset({
    "in", "then", "else", "requires", "ensures", "decreases", "reads",
    "returns", "forall", "exists", "if", "case", "match",
})


def _is_value_ender(token: str | None) -> bool:
    if token is None:
        return False
    if token in (")", "]", ">"):
        return True
    if token.isdigit():
        return True
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", token)) \
        and token not in _SIDECAR_NON_ENDERS


def _validate_sidecar(text: str, name: str) -> frozenset[str]:
    """Whitelist-structural validation of a proof sidecar. Returns declared
    lemma names. Rejects (a) any non-ghost or trust-bypassing token —
    method/import/assume/{:attributes}/... — and (b) bodiless declarations
    (a lemma without a body is an axiom)."""
    stripped = _strip_dafny_comments(text)
    if "{:" in stripped:
        raise EncodeError(f"proof sidecar {name}: attributes ({{:...}}) are not allowed")
    if "@" in stripped:
        # Verbatim @-strings don't use backslash escapes and would evade the
        # string blanking above; nothing a lemma pack needs uses `@`.
        raise EncodeError(f"proof sidecar {name}: `@` is not allowed")
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_']*|\{|\}|.", stripped)
    words = [t for t in tokens if t.strip()]
    for w in words:
        if w in _SIDECAR_FORBIDDEN:
            raise EncodeError(
                f"proof sidecar {name}: {w!r} is not allowed — sidecars may "
                f"contain only proved ghost declarations (lemma/function/predicate)"
            )
        if w == "~":
            raise EncodeError(f"proof sidecar {name}: partial-arrow types are not allowed")
    for i in range(len(words) - 1):
        # An isolated `=>` is a lambda (its body brace follows a `>`, which
        # would defeat the value-ender body check); `==>` (implication) has a
        # preceding `=` and stays legal.
        if words[i] == "=" and words[i + 1] == ">" \
                and (i == 0 or words[i - 1] != "="):
            raise EncodeError(
                f"proof sidecar {name}: lambda expressions (`=>`) are not allowed"
            )
    lemmas: set[str] = set()
    depth = 0
    expecting_decl = True  # at file start and after every body closes
    current_decl_has_body = True  # vacuously, before any declaration
    idx = 0
    while idx < len(words):
        w = words[idx]
        if w == "{":
            if depth == 0:
                # A body brace always follows a value-ender; a brace after an
                # operator/keyword (`in {1, 2}`) is a specification literal —
                # which would let a BODILESS lemma masquerade as proved.
                prev = words[idx - 1] if idx > 0 else None
                if not _is_value_ender(prev):
                    raise EncodeError(
                        f"proof sidecar {name}: brace-delimited literals in "
                        f"specification position are not supported — a bodiless "
                        f"declaration could masquerade as proved; restate the "
                        f"spec without set/map displays"
                    )
                current_decl_has_body = True
            depth += 1
        elif w == "}":
            depth = max(0, depth - 1)
            if depth == 0:
                expecting_decl = True
        elif depth == 0 and w in _SIDECAR_DECL_KEYWORDS:
            # A declaration keyword at depth 0 ALWAYS starts a new
            # declaration — checking the previous one here means a bodiless
            # lemma cannot be retroactively "proved" by its successor's body.
            if not current_decl_has_body:
                raise EncodeError(
                    f"proof sidecar {name}: a declaration without a body is an "
                    f"axiom — every lemma/function must be proved"
                )
            if w == "ghost":
                if idx + 1 >= len(words) or words[idx + 1] not in ("function", "predicate"):
                    raise EncodeError(f"proof sidecar {name}: `ghost` must qualify function/predicate")
                idx += 1
            if w == "lemma" and idx + 1 < len(words):
                lemmas.add(words[idx + 1])
            expecting_decl = False
            current_decl_has_body = False
        elif depth == 0 and expecting_decl:
            raise EncodeError(
                f"proof sidecar {name}: top-level {w!r} is not a ghost "
                f"declaration (lemma/function/predicate)"
            )
        idx += 1
    if not current_decl_has_body:
        raise EncodeError(
            f"proof sidecar {name}: a declaration without a body is an axiom — "
            f"every lemma/function must be proved"
        )
    return frozenset(lemmas)


def load_proof_sidecar(source_path: Path) -> ProofSidecar:
    """Proof additions from `<stem>.proofs.dfy` beside the source file:
    lemma packs referenced by `#@ proof` clauses. Whitelist-validated as
    proved ghost declarations only."""
    sidecar = source_path.with_name(source_path.stem + ".proofs.dfy")
    if not sidecar.exists():
        return ProofSidecar.empty()
    text = sidecar.read_text()
    lemmas = _validate_sidecar(text, sidecar.name)
    return ProofSidecar(
        f"\n// ---- proof additions from {sidecar.name} ----\n{text}", lemmas
    )

DAFNY_KEYWORDS = frozenset({
    "method", "function", "lemma", "var", "ghost", "returns", "requires",
    "ensures", "invariant", "decreases", "reads", "modifies", "assert",
    "assume", "while", "forall", "exists", "match", "case", "int", "bool",
    "string", "seq", "set", "map", "old", "then", "print", "new", "this",
    "char", "nat", "real", "type", "datatype", "predicate", "true", "false",
})


class EncodeError(Exception):
    def __init__(self, message: str, line: int | None = None):
        super().__init__(message)
        self.message = message
        self.line = line


def _err(node: ast.AST, message: str) -> EncodeError:
    return EncodeError(message, getattr(node, "lineno", None))


def _dafny_type(ann: ast.expr | None, where: ast.AST) -> str:
    if ann is None:
        raise _err(where, "missing type annotation (the fragment requires precise types)")
    match ann:
        case ast.Name(id="int"):
            return "int"
        case ast.Name(id="bool"):
            return "bool"
        case ast.Name(id="str"):
            return "string"
        case ast.Subscript(value=ast.Name(id="list"), slice=inner):
            return f"seq<{_dafny_type(inner, where)}>"
        case ast.Subscript(value=ast.Name(id="Optional"), slice=inner):
            return f"PyOpt<{_dafny_type(inner, where)}>"
        case ast.BinOp(left=left, op=ast.BitOr(), right=ast.Constant(value=None)):
            return f"PyOpt<{_dafny_type(left, where)}>"
        case ast.BinOp(left=ast.Constant(value=None), op=ast.BitOr(), right=right):
            return f"PyOpt<{_dafny_type(right, where)}>"
        case _:
            raise _err(where, f"type {ast.unparse(ann)!r} is outside the slice-1 encoder")


def _opt_inner(tdesc: str | None) -> str | None:
    """PyOpt<T> -> T, else None."""
    if tdesc is not None and tdesc.startswith("PyOpt<") and tdesc.endswith(">"):
        return tdesc[6:-1]
    return None


_INT_SET = frozenset({"int"})
_ORDER_OK = frozenset({"int", "char"})


@dataclass
class _Scope:
    names: set[str]


_ENCODED_BUILTINS = frozenset({
    "len", "min", "max", "abs", "sum", "range", "bool", "all", "any", "old",
})


class _MethodEncoder:
    def __init__(self, node: ast.FunctionDef, spec: FunctionSpec,
                 proof_lemmas: frozenset[str] = frozenset(),
                 source_lines: list[str] | None = None):
        self.node = node
        self.spec = spec
        self.proof_lemmas = proof_lemmas
        self.source_lines = source_lines or []
        self.lines: list[str] = []
        self.line_map: dict[int, int] = {}  # emitted index -> python line
        self.params: set[str] = {
            p.arg for p in (*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs)
        }
        # The encoder resolves these names to Dafny builtins by name alone,
        # so no binding in the function may reuse them.
        for p in sorted(self.params & _ENCODED_BUILTINS):
            raise EncodeError(
                f"parameter {p!r} shadows a builtin the encoder gives meaning "
                f"to — rename it", node.lineno)
        for n in ast.walk(node):
            bound: list[str] = []
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
                bound = [n.id]
            elif isinstance(n, (ast.MatchAs, ast.MatchStar)) and n.name:
                bound = [n.name]  # match/import are outside the fragment,
            elif isinstance(n, ast.MatchMapping) and n.rest:
                bound = [n.rest]  # but the scan must not trail it
            elif isinstance(n, (ast.Import, ast.ImportFrom)):
                bound = [(a.asname or a.name).split(".")[0] for a in n.names]
            for name in bound:
                if name in _ENCODED_BUILTINS:
                    raise _err(n, (
                        f"binding {name!r} shadows a builtin the encoder gives "
                        f"meaning to — rename it"
                    ))
            if isinstance(n, (ast.Global, ast.Nonlocal)) \
                    and set(n.names) & _ENCODED_BUILTINS:
                raise _err(n, "global/nonlocal on a builtin name is outside the fragment")
        self.types: dict[str, str | None] = {}
        self.scopes: list[set[str]] = [set()]
        self.retired: set[str] = set()
        self.spec_mode = False
        self.return_type: str | None = None

        self.used_names = self._collect_used_names()
        self.mangle_map = self._build_mangle_map()
        self._invariants_by_loop: dict[int, list[Clause]] = {}
        self._decreases_by_loop: dict[int, list[Clause]] = {}
        self._assign_loop_clauses()
        # `#@ proof` clauses: AST-anchored to the exact statement they
        # precede, so they can never drift into an enclosing/sibling scope.
        self._proofs_by_stmt: dict[int, list[Clause]] = {}
        self._assign_proof_clauses()
        self.hoisted: dict[str, str] = {}
        # Ownership-lite (§3.2, conservative): a list local may be appended
        # to only while it is a fresh, unaliased allocation.
        self.owned: set[str] = set()
        # Containers currently being iterated by an enclosing for-each —
        # mutating them mid-iteration is rejected (§3.2).
        self.frozen: set[str] = set()
        # Comprehension binders: raw name -> dafny expression to substitute.
        self.name_overrides: dict[str, str] = {}
        # Names provably >= 0 (0-based loop indices, 0-based quantifier
        # binders): indexed bare, keeping spec and body terms trigger-
        # compatible; everything else goes through PyIndex.
        self.nonneg: set[str] = set()

    # -- naming ---------------------------------------------------------------

    def _collect_used_names(self) -> set[str]:
        names: set[str] = set(self.params)
        for n in ast.walk(self.node):
            if isinstance(n, ast.Name):
                names.add(n.id)
        for clause in self.spec.clauses:
            if clause.desugared:
                try:
                    tree = ast.parse(clause.desugared, mode="eval")
                except SyntaxError:
                    continue
                for n in ast.walk(tree):
                    if isinstance(n, ast.Name):
                        names.add(n.id)
        return names

    def _build_mangle_map(self) -> dict[str, str]:
        mapping: dict[str, str] = {}
        taken = set(self.used_names)
        for name in sorted(self.used_names):
            if name in DAFNY_KEYWORDS:
                candidate = f"{name}_py"
                while candidate in taken:
                    candidate += "_"
                mapping[name] = candidate
                taken.add(candidate)
        return mapping

    def _mangle(self, name: str) -> str:
        return self.mangle_map.get(name, name)

    def _fresh(self, base: str) -> str:
        candidate = base
        taken = self.used_names | set(self.mangle_map.values())
        while candidate in taken:
            candidate += "_"
        self.used_names.add(candidate)
        return candidate

    # -- scoping ----------------------------------------------------------------

    def _declared(self, name: str) -> bool:
        return any(name in scope for scope in self.scopes)

    def _declare(self, name: str) -> None:
        self.scopes[-1].add(name)

    # -- clause-to-loop attachment ------------------------------------------------

    def _assign_loop_clauses(self) -> None:
        loops = [n for n in ast.walk(self.node) if isinstance(n, (ast.While, ast.For))]
        for kind, store in (("invariant", self._invariants_by_loop),
                            ("decreases", self._decreases_by_loop)):
            for clause in self.spec.by_kind(kind):
                owner: ast.While | ast.For | None = None
                for loop in loops:
                    if loop.body and loop.lineno < clause.line < loop.body[0].lineno:
                        owner = loop  # spans cannot overlap here: header-to-first-stmt gaps nest uniquely
                if owner is None:
                    raise EncodeError(
                        f"`{kind}` must sit at the top of a loop body, before its "
                        f"first statement (found none containing this line)",
                        clause.line,
                    )
                store.setdefault(id(owner), []).append(clause)

    # -- conservative type inference ------------------------------------------------

    def _infer(self, node: ast.expr) -> str | None:
        match node:
            case ast.Constant(value=bool()):
                return "bool"
            case ast.Constant(value=int()):
                return "int"
            case ast.Constant(value=str()):
                return "string"
            case ast.Name(id="result") if self.spec_mode:
                return self.return_type
            case ast.Name(id=name):
                return self.types.get(name)
            case ast.UnaryOp(op=ast.Not()):
                return "bool"
            case ast.UnaryOp(op=ast.USub(), operand=operand):
                return "int" if self._infer(operand) == "int" else None
            case ast.BoolOp() | ast.Compare():
                return "bool"
            case ast.BinOp(left=left, op=op, right=right):
                lt, rt = self._infer(left), self._infer(right)
                if isinstance(op, (ast.FloorDiv, ast.Mod)):
                    return "int" if lt == "int" and rt == "int" else None
                if isinstance(op, ast.Add) and lt == rt and lt is not None \
                        and (lt == "string" or lt.startswith("seq<")):
                    return lt  # concatenation: same meaning in both languages
                if lt == "int" and rt == "int":
                    return "int"
                return None
            case ast.Call(func=ast.Name(id="len")):
                return "int"
            case ast.Call(func=ast.Name(id=("min" | "max" | "abs" | "sum"))):
                return "int"
            case ast.Call(func=ast.Name(id="bool")):
                return "bool"
            case ast.Call(func=ast.Name(id=("all" | "any"))):
                return "bool"
            case ast.Call(func=ast.Name(id="old"), args=[ast.Name(id=name)]):
                return self.types.get(name)
            case ast.Subscript(value=value, slice=ast.Slice()):
                return self._infer(value)  # a slice keeps the sequence type
            case ast.Subscript(value=value):
                base = self._infer(value)
                if base == "string":
                    return "char"
                if base is not None and base.startswith("seq<"):
                    return base[4:-1]
                return None
            case ast.IfExp(body=body, orelse=orelse):
                bt, ot = self._infer(body), self._infer(orelse)
                return bt if bt == ot else None
            case ast.List(elts=elts):
                inner = {self._infer(e) for e in elts}
                if len(inner) == 1 and None not in inner:
                    return f"seq<{inner.pop()}>"
                return None
            case ast.ListComp(elt=elt, generators=[comp]) if not comp.ifs:
                binder_type = self._comp_binder_type(comp)
                if binder_type is None or not isinstance(comp.target, ast.Name):
                    return None
                saved = self.types.get(comp.target.id)
                self.types[comp.target.id] = binder_type
                try:
                    et = self._infer(elt)
                finally:
                    if saved is None:
                        self.types.pop(comp.target.id, None)
                    else:
                        self.types[comp.target.id] = saved
                return f"seq<{et}>" if et is not None else None
            case _:
                return None

    def _comp_binder_type(self, comp: ast.comprehension) -> str | None:
        it = comp.iter
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) \
                and it.func.id == "range" and 1 <= len(it.args) <= 2 \
                and not it.keywords:
            return "int"
        dt = self._infer(it)
        if dt is not None and dt.startswith("seq<"):
            return dt[4:-1]
        return None

    def _is_seqish(self, tdesc: str | None) -> bool:
        return tdesc is not None and (tdesc == "string" or tdesc.startswith("seq<"))

    # -- emission helpers --------------------------------------------------------------

    def emit(self, text: str, py_line: int | None = None) -> None:
        self.lines.append(text)
        if py_line is not None:
            self.line_map[len(self.lines) - 1] = py_line

    # -- expressions ---------------------------------------------------------------------

    def expr(self, node: ast.expr) -> str:
        match node:
            case ast.Constant(value=bool() as b):
                return "true" if b else "false"
            case ast.Constant(value=int() as i):
                return str(i)
            case ast.Constant(value=str() as s):
                return self._escape_str(s, node)
            case ast.Name(id=name):
                if name in self.name_overrides:
                    return self.name_overrides[name]
                if name == "result":
                    if not self.spec_mode:
                        raise _err(node, "`result` is spec-only")
                    return "result"
                if name in self.retired:
                    raise _err(node, (
                        f"loop index {name!r} used after its loop — Python leaves it at "
                        f"the last iterated value (or unbound), the lowering does not; "
                        f"outside the slice-1 encoder"
                    ))
                return self._mangle(name)
            case ast.UnaryOp(op=ast.Not(), operand=operand):
                if self._is_seqish(self._infer(operand)):
                    # §7.3 truthiness: `not xs` on a list/str means emptiness.
                    return f"(|{self.expr(operand)}| == 0)"
                return f"!({self.expr(operand)})"
            case ast.UnaryOp(op=ast.USub(), operand=operand):
                return f"(-{self.expr(operand)})"
            case ast.BoolOp(op=op, values=values):
                for v in values:
                    if self._is_seqish(self._infer(v)):
                        raise _err(node, (
                            "and/or on list/str operands returns an operand "
                            "(§7.3 truthiness); outside the slice-1 encoder"
                        ))
                joiner = " && " if isinstance(op, ast.And) else " || "
                return "(" + joiner.join(f"({self.expr(v)})" for v in values) + ")"
            case ast.BinOp(left=left, op=op, right=right):
                l, r = self._deopt(left), self._deopt(right)
                match op:
                    case ast.Add():
                        return f"({l} + {r})"
                    case ast.Sub():
                        return f"({l} - {r})"
                    case ast.Mult():
                        return f"({l} * {r})"
                    case ast.FloorDiv():
                        return f"PyFloorDiv({l}, {r})"
                    case ast.Mod():
                        return f"PyMod({l}, {r})"
                    case _:
                        raise _err(node, f"operator {type(op).__name__} is outside the slice-1 encoder")
            case ast.Compare(left=left, ops=ops, comparators=comps):
                return self._compare(node, left, ops, comps)
            case ast.Call():
                return self._call(node)
            case ast.IfExp(test=test, body=body, orelse=orelse):
                return f"(if {self.expr(test)} then {self.expr(body)} else {self.expr(orelse)})"
            case ast.Subscript(value=value, slice=index):
                if isinstance(index, ast.Slice):
                    if index.step is not None:
                        raise _err(node, "slice steps are outside the slice encoder")
                    base = self.expr(value)
                    lo = self.expr(index.lower) if index.lower is not None else "0"
                    hi = self.expr(index.upper) if index.upper is not None else f"|{base}|"
                    return f"PySlice({base}, {lo}, {hi})"
                base = self.expr(value)
                idx = self.expr(index)
                # Python normalizes negative indices from the end; Dafny does
                # not. PyIndex carries Python's exact semantics (its requires
                # is exactly Python's IndexError condition). Indices provably
                # >= 0 — nonneg literals and tracked 0-based binders/loop
                # variables — are emitted BARE so spec quantifier triggers
                # match the body's ground terms; everything else is wrapped.
                provably_nonneg = (
                    isinstance(index, ast.Constant)
                    and isinstance(index.value, int) and index.value >= 0
                ) or (
                    isinstance(index, ast.Name) and index.id in self.nonneg
                )
                if provably_nonneg:
                    return f"{base}[{idx}]"
                return f"{base}[PyIndex({idx}, |{base}|)]"
            case ast.List(elts=elts):
                return "[" + ", ".join(self.expr(e) for e in elts) + "]"
            case ast.ListComp(elt=elt, generators=[comp]) if not comp.ifs \
                    and not comp.is_async and isinstance(comp.target, ast.Name):
                return self._list_comp(node, elt, comp)
            case ast.ListComp():
                raise _err(node, "only single-generator, filterless list comprehensions are in the slice encoder")
            case _:
                raise _err(node, f"expression {type(node).__name__} is outside the slice-1 encoder")

    def _list_comp(self, node: ast.ListComp | ast.GeneratorExp, elt: ast.expr,
                   comp: ast.comprehension, require_int_elt: bool = False) -> str:
        raw = comp.target.id  # type: ignore[union-attr]
        if raw in self.params or self._declared(raw) \
                or raw in self.name_overrides or raw in self.types:
            raise _err(node, (
                f"comprehension binder {raw!r} shadows an existing name — "
                f"rename the binder"
            ))
        it = comp.iter
        idx = self._fresh(f"{raw}_c")
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) \
                and it.func.id == "range" and 1 <= len(it.args) <= 2 \
                and not it.keywords:
            if len(it.args) == 1:
                lo, hi = "0", self.expr(it.args[0])
            else:
                lo, hi = self.expr(it.args[0]), self.expr(it.args[1])
            count = f"PyMax(0, ({hi}) - ({lo}))"
            override = f"(({lo}) + {idx})"
            binder_type: str | None = "int"
        else:
            dt = self._infer(it)
            if not (dt is not None and dt.startswith("seq<")):
                raise _err(node, "comprehension sources must be range(...) or a list")
            src = self.expr(it)
            count = f"|{src}|"
            override = f"{src}[{idx}]"
            binder_type = dt[4:-1]
        saved_override = self.name_overrides.get(raw)
        saved_type = self.types.get(raw)
        self.name_overrides[raw] = override
        self.types[raw] = binder_type
        try:
            if require_int_elt:
                if self._eff_type(elt) != "int":
                    raise _err(node, "sum() needs an int-valued generator expression")
                # Optional[int] elements project through .v — the well-
                # formedness VC is Python's would-raise-TypeError condition.
                body = self._deopt(elt)
            else:
                body = self.expr(elt)
        finally:
            if saved_override is None:
                self.name_overrides.pop(raw, None)
            else:
                self.name_overrides[raw] = saved_override
            if saved_type is None:
                self.types.pop(raw, None)
            else:
                self.types[raw] = saved_type
        return f"seq({count}, {idx} requires 0 <= {idx} < {count} => {body})"

    def _escape_str(self, value: str, node: ast.expr) -> str:
        out = []
        for ch in value:
            if ch == "\\":
                out.append("\\\\")
            elif ch == '"':
                out.append('\\"')
            elif ch == "\n":
                out.append("\\n")
            elif ch == "\t":
                out.append("\\t")
            elif ord(ch) < 0x20 or ord(ch) == 0x7F:
                raise _err(node, f"control character {ch!r} in string literal is outside the slice-1 encoder")
            else:
                out.append(ch)
        return '"' + "".join(out) + '"'

    def _eff_type(self, node: ast.expr) -> str | None:
        """Inferred type with PyOpt<T> flattened to T (deopt semantics)."""
        t = self._infer(node)
        return _opt_inner(t) or t

    def _deopt(self, node: ast.expr) -> str:
        """Encode node, projecting PyOpt<T> to T. The `.v` well-formedness VC
        is exactly Python's would-raise-TypeError condition — narrowing
        replayed as a proof obligation."""
        if _opt_inner(self._infer(node)) is not None:
            return f"({self.expr(node)}).v"
        return self.expr(node)

    def _compare(self, node: ast.Compare, left: ast.expr, ops, comps) -> str:
        parts = []
        current = left
        for op, comp in zip(ops, comps):
            if isinstance(op, (ast.Is, ast.IsNot)):
                # Only `x is [not] None` on an Optional is in the fragment.
                if isinstance(comp, ast.Constant) and comp.value is None \
                        and _opt_inner(self._infer(current)) is not None:
                    tester = "PyNone?" if isinstance(op, ast.Is) else "PySome?"
                    parts.append(f"({self.expr(current)}).{tester}")
                    current = comp
                    continue
                raise _err(node, (
                    "`is` is only supported as `is [not] None` on Optional-typed "
                    "values; identity on other objects is outside the fragment"
                ))
            if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                lt, rt = self._eff_type(current), self._eff_type(comp)
                if not (lt in _ORDER_OK and lt == rt):
                    raise _err(node, (
                        f"order comparison on non-int operands (inferred {lt}/{rt}) — "
                        f"Dafny's sequence `<` is prefix order, Python's is lexicographic; "
                        f"outside the slice-1 encoder"
                    ))
                l, r = self._deopt(current), self._deopt(comp)
            elif isinstance(op, (ast.Eq, ast.NotEq)):
                lt, rt = self._infer(current), self._infer(comp)
                if _opt_inner(lt) is not None and _opt_inner(lt) == rt:
                    # Python's == never raises: Optional-vs-T equality means
                    # "is Some AND the payload matches".
                    inner = f"(({self.expr(current)}).PySome? && ({self.expr(current)}).v == {self.expr(comp)})"
                    parts.append(inner if isinstance(op, ast.Eq) else f"!{inner}")
                    current = comp
                    continue
                if _opt_inner(rt) is not None and _opt_inner(rt) == lt:
                    inner = f"(({self.expr(comp)}).PySome? && ({self.expr(comp)}).v == {self.expr(current)})"
                    parts.append(inner if isinstance(op, ast.Eq) else f"!{inner}")
                    current = comp
                    continue
                l, r = self.expr(current), self.expr(comp)
            else:
                l, r = self.expr(current), self.expr(comp)
            match op:
                case ast.Eq():
                    parts.append(f"{l} == {r}")
                case ast.NotEq():
                    parts.append(f"{l} != {r}")
                case ast.Lt():
                    parts.append(f"{l} < {r}")
                case ast.LtE():
                    parts.append(f"{l} <= {r}")
                case ast.Gt():
                    parts.append(f"{l} > {r}")
                case ast.GtE():
                    parts.append(f"{l} >= {r}")
                case ast.In() | ast.NotIn():
                    rt = self._infer(comp)
                    if rt is None or not rt.startswith("seq<"):
                        raise _err(node, (
                            "`in` is only supported against list operands (Python's "
                            "`in` on str means substring, Dafny's means element); "
                            "outside the slice-1 encoder"
                        ))
                    parts.append(f"{l} {'in' if isinstance(op, ast.In) else '!in'} {r}")
                case _:
                    raise _err(node, f"comparison {type(op).__name__} is outside the fragment")
            current = comp
        return "(" + " && ".join(parts) + ")" if len(parts) > 1 else f"({parts[0]})"

    def _call(self, node: ast.Call) -> str:
        func = node.func
        if not isinstance(func, ast.Name):
            raise _err(node, "method calls are outside the slice-1 encoder")
        name = func.id
        args = node.args
        if node.keywords:
            # No encoded builtin takes keywords; silently dropping one
            # (e.g. max(a, b, key=abs)) would change the meaning.
            raise _err(node, f"keyword arguments to {name}() are outside the fragment")
        if name == "len" and len(args) == 1:
            return f"|{self.expr(args[0])}|"
        if name in ("min", "max") and len(args) == 2:
            for a in args:
                if self._eff_type(a) != "int":
                    raise _err(node, f"{name}() on non-int operands is outside the slice-1 encoder")
            fn = "PyMin" if name == "min" else "PyMax"
            return f"{fn}({self._deopt(args[0])}, {self._deopt(args[1])})"
        if name in ("min", "max") and len(args) == 1:
            if self._infer(args[0]) != "seq<int>":
                raise _err(node, f"1-arg {name}() needs a list[int] operand in the slice encoder")
            fn = "PySeqMin" if name == "min" else "PySeqMax"
            # PySeqMax/Min's requires (|s| >= 1) is Python's ValueError condition.
            return f"{fn}({self.expr(args[0])})"
        if name == "abs" and len(args) == 1:
            return f"PyAbs({self.expr(args[0])})"
        if name == "sum" and len(args) == 1:
            arg = args[0]
            if isinstance(arg, ast.GeneratorExp):
                if len(arg.generators) != 1 or arg.generators[0].ifs \
                        or arg.generators[0].is_async \
                        or not isinstance(arg.generators[0].target, ast.Name):
                    raise _err(node, (
                        "sum() accepts only single-generator, filterless "
                        "generator expressions in the slice encoder"
                    ))
                mapped = self._list_comp(arg, arg.elt, arg.generators[0],
                                         require_int_elt=True)
                return f"PySum({mapped})"
            if self._infer(arg) != "seq<int>":
                raise _err(node, "sum() needs a list[int] operand in the slice encoder")
            return f"PySum({self.expr(arg)})"
        if name == "old" and self.spec_mode and len(args) == 1 and isinstance(args[0], ast.Name):
            # Parameters are immutable in the fragment (ownership + copy-in).
            if args[0].id not in self.params:
                raise _err(node, "old() takes a parameter name")
            return self._mangle(args[0].id)
        if name == "bool" and self.spec_mode and len(args) == 1:
            if self._infer(args[0]) != "bool":
                raise _err(node, (
                    "truthiness in specs is outside the fragment — write an explicit "
                    "comparison (e.g. `x != 0`) instead of relying on bool(<non-bool>)"
                ))
            return f"({self.expr(args[0])})"
        if name in ("all", "any") and self.spec_mode and len(args) == 1 \
                and isinstance(args[0], ast.GeneratorExp):
            return self._quantifier(name, args[0])
        raise _err(node, f"call to {name!r} is outside the slice-1 encoder")

    def _quantifier(self, kind: str, gen: ast.GeneratorExp) -> str:
        binders: list[str] = []
        domains: list[str] = []
        binder_names: list[str] = []
        saved_types: dict[str, str | None] = {}
        try:
            for comp in gen.generators:
                if comp.ifs:
                    raise _err(gen, "quantifier `if` guards are outside the slice-1 encoder")
                if comp.is_async or not isinstance(comp.target, ast.Name):
                    raise _err(gen, "unsupported quantifier binder")
                raw = comp.target.id
                # name_overrides/types catch enclosing comprehension and
                # quantifier binders: an override would silently rewrite
                # every occurrence of this binder in the body.
                if raw in self.params or self._declared(raw) or raw in binder_names \
                        or raw in self.name_overrides or raw in self.types:
                    raise _err(gen, (
                        f"quantifier binder {raw!r} shadows an existing name — Python "
                        f"evaluates the domain in the enclosing scope, the Dafny binder "
                        f"would capture it; rename the binder"
                    ))
                var = self._mangle(raw)
                domain = comp.iter
                if isinstance(domain, ast.Call) and isinstance(domain.func, ast.Name) \
                        and domain.func.id == "range" and 1 <= len(domain.args) <= 2 \
                        and not domain.keywords:
                    if len(domain.args) == 1:
                        lo, hi = "0", self.expr(domain.args[0])
                    else:
                        lo, hi = self.expr(domain.args[0]), self.expr(domain.args[1])
                    domains.append(f"{lo} <= {var} < {hi}")
                    binder_type: str | None = "int"
                    if lo == "0" or (lo.lstrip("(").rstrip(")").isdigit()):
                        self.nonneg.add(raw)
                else:
                    dt = self._infer(domain)
                    if dt is None or not dt.startswith("seq<"):
                        raise _err(gen, "quantifier domains must be range(...) or a list")
                    domains.append(f"{var} in {self.expr(domain)}")
                    binder_type = dt[4:-1]
                binders.append(var)
                binder_names.append(raw)
                saved_types[raw] = self.types.get(raw)
                self.types[raw] = binder_type
            body = self.expr(gen.elt)
        finally:
            for raw in binder_names:
                prev = saved_types.get(raw)
                if prev is None:
                    self.types.pop(raw, None)
                else:
                    self.types[raw] = prev
                self.nonneg.discard(raw)
        quant = "forall" if kind == "all" else "exists"
        connective = "==>" if kind == "all" else "&&"
        return f"({quant} {', '.join(binders)} :: ({' && '.join(domains)}) {connective} ({body}))"

    # -- specs -------------------------------------------------------------------------------

    def spec_expr(self, clause: Clause) -> str:
        assert clause.desugared is not None
        tree = ast.parse(clause.desugared, mode="eval")
        self.spec_mode = True
        try:
            return self.expr(tree.body)
        except EncodeError as exc:
            raise EncodeError(exc.message, clause.line) from exc
        finally:
            self.spec_mode = False

    # -- hoisting analysis (Dafny block scoping vs Python function scoping) --------------------

    def _hoist_analysis(self) -> dict[str, str]:
        stores: dict[str, list[tuple]] = {}
        loads: dict[str, list[tuple]] = {}
        first_rhs: dict[str, ast.expr] = {}
        ann_types: dict[str, str] = {}
        loop_indices: set[str] = set()

        def record_store(name: str, path: tuple, rhs: ast.expr | None, stmt: ast.stmt) -> None:
            stores.setdefault(name, []).append(path)
            if rhs is not None and name not in first_rhs:
                first_rhs[name] = rhs

        def record_expr_loads(node: ast.AST, path: tuple) -> None:
            for n in ast.walk(node):
                if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                    loads.setdefault(n.id, []).append(path)

        def walk(stmts: list[ast.stmt], path: tuple) -> None:
            for idx, stmt in enumerate(stmts):
                match stmt:
                    case ast.Assign(targets=[ast.Name(id=name)], value=value):
                        record_store(name, path, value, stmt)
                        record_expr_loads(value, path)
                    case ast.Assign(targets=[ast.Tuple(elts=elts)], value=value):
                        vals = value.elts if isinstance(value, ast.Tuple) else []
                        for j, e in enumerate(elts):
                            if isinstance(e, ast.Name):
                                record_store(e.id, path, vals[j] if j < len(vals) else None, stmt)
                        record_expr_loads(value, path)
                    case ast.AnnAssign(target=ast.Name(id=name), annotation=ann, value=value):
                        record_store(name, path, value, stmt)
                        try:
                            ann_types[name] = _dafny_type(ann, stmt)
                        except EncodeError:
                            pass
                        if value is not None:
                            record_expr_loads(value, path)
                    case ast.AugAssign(target=ast.Name(id=name), value=value):
                        record_store(name, path, None, stmt)
                        loads.setdefault(name, []).append(path)
                        record_expr_loads(value, path)
                    case ast.If(test=test, body=body, orelse=orelse):
                        record_expr_loads(test, path)
                        walk(body, path + (idx, "t"))
                        walk(orelse, path + (idx, "e"))
                    case ast.While(test=test, body=body):
                        record_expr_loads(test, path)
                        walk(body, path + (idx, "w"))
                    case ast.For(target=ast.Name(id=name), iter=it, body=body):
                        loop_indices.add(name)
                        record_expr_loads(it, path)
                        walk(body, path + (idx, "f"))
                    case _:
                        record_expr_loads(stmt, path)

        walk(self.node.body, ())

        hoisted: dict[str, str] = {}
        for name, paths in stores.items():
            if name in self.params or name in loop_indices:
                continue
            all_access = paths + loads.get(name, [])
            shortest = min(paths, key=len)
            needs_hoist = any(p[:len(shortest)] != shortest for p in all_access) or (
                len({tuple(p) for p in paths}) > 1
                and any(p[:len(shortest)] != shortest for p in paths)
            )
            if not needs_hoist:
                continue
            dtype = ann_types.get(name)
            if dtype is None and name in first_rhs:
                # Seed parameter types so inference over the first RHS works.
                dtype = self._infer(first_rhs[name])
            if dtype is None:
                raise EncodeError(
                    f"cannot infer a type for {name!r} (assigned across branches); "
                    f"annotate its first assignment",
                    self.node.lineno,
                )
            hoisted[name] = dtype
        return hoisted

    # -- statements -------------------------------------------------------------------------------

    def _assign_proof_clauses(self) -> None:
        """Anchor each `#@ proof` clause to the statement it lexically
        precedes; a clause not followed by a statement in its block is a
        detected error, never a scope leak."""
        clauses = sorted(self.spec.by_kind("proof"), key=lambda c: c.line)
        if not clauses:
            return
        for clause in clauses:
            tree = ast.parse(clause.desugared, mode="eval")
            assert isinstance(tree.body, ast.Call) and isinstance(tree.body.func, ast.Name)
            target = tree.body.func.id
            if target not in self.proof_lemmas:
                raise EncodeError(
                    f"unknown lemma {target!r} — `#@ proof` targets must be "
                    f"lemmas declared in the proof sidecar (<stem>.proofs.dfy)",
                    clause.line,
                )
        unattached = {id(c): c for c in clauses}

        def visit(stmts: list[ast.stmt], header_line: int, territory_end: int) -> None:
            """Attach clauses whose COLUMN matches this block's indentation
            and whose line falls in this block's territory — column is what
            distinguishes 'trailing inside the inner block' from 'between
            statements of the outer one'."""
            col = min(s.col_offset for s in stmts)
            for clause in list(unattached.values()):
                if clause.col == col and header_line < clause.line < territory_end:
                    following = [s for s in stmts if s.lineno > clause.line]
                    if not following:
                        raise EncodeError(
                            "`#@ proof` must directly precede the statement it "
                            "justifies (this one trails its block)",
                            clause.line,
                        )
                    self._proofs_by_stmt.setdefault(id(following[0]), []).append(clause)
                    del unattached[id(clause)]
            for i, s in enumerate(stmts):
                next_boundary = stmts[i + 1].lineno if i + 1 < len(stmts) else territory_end
                match s:
                    case ast.For(body=body) | ast.While(body=body):
                        visit(body, s.lineno, next_boundary)
                    case ast.If(body=body, orelse=orelse):
                        if orelse:
                            # The then/else territories split at the `else:`
                            # line — a clause LEADING the else branch must not
                            # be claimed as TRAILING the then branch (same
                            # column, so only the else line disambiguates).
                            else_line = orelse[0].lineno
                            for ln in range((body[-1].end_lineno or s.lineno) + 1,
                                            orelse[0].lineno):
                                if 0 < ln <= len(self.source_lines) \
                                        and re.match(r"\s*else\s*:", self.source_lines[ln - 1]):
                                    else_line = ln
                                    break
                            visit(body, s.lineno, else_line)
                            visit(orelse, else_line, next_boundary)
                        else:
                            visit(body, s.lineno, next_boundary)
                    case _:
                        pass

        visit(self.node.body, self.node.lineno, (self.node.end_lineno or self.node.lineno) + 1)
        if unattached:
            first = next(iter(unattached.values()))
            raise EncodeError(
                "`#@ proof` could not be attached to a statement — align it "
                "with the block it belongs to, directly before a statement",
                first.line,
            )

    def _emit_proof(self, clause: Clause, indent: str) -> None:
        tree = ast.parse(clause.desugared, mode="eval")
        call = tree.body
        assert isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
        self.spec_mode = True
        try:
            args = ", ".join(self.expr(a) for a in call.args)
        finally:
            self.spec_mode = False
        # The lemma name is Dafny-side (validated against the sidecar's
        # declared lemmas) — never mangled; ghost, so it cannot affect state.
        self.emit(f"{indent}{call.func.id}({args});", clause.line)

    def block(self, stmts: list[ast.stmt], indent: str) -> None:
        self.scopes.append(set())
        try:
            for stmt in stmts:
                self.stmt(stmt, indent)
        finally:
            self.scopes.pop()

    def _assign_name(self, name: str, rhs: str, indent: str, stmt: ast.stmt,
                     rhs_node: ast.expr | None = None, ann: str | None = None) -> None:
        if name in self.params:
            raise _err(stmt, "parameter rebinding is outside the fragment (parameters are immutable)")
        if isinstance(rhs_node, ast.List) and not rhs_node.elts and ann is None \
                and self.types.get(name) is None:
            raise _err(stmt, f"annotate the empty list (`{name}: list[...] = []`) — its element type is undecidable")
        self.retired.discard(name)
        if name in self.hoisted or self._declared(name):
            self.emit(f"{indent}{self._mangle(name)} := {rhs};", stmt.lineno)
        else:
            type_note = f": {ann}" if ann else ""
            self.emit(f"{indent}var {self._mangle(name)}{type_note} := {rhs};", stmt.lineno)
            self._declare(name)
        if name not in self.types:
            self.types[name] = ann or (self._infer(rhs_node) if rhs_node is not None else None)
        self._update_ownership(name, rhs_node)

    def _update_ownership(self, name: str, rhs_node: ast.expr | None) -> None:
        """Ownership-lite: fresh allocations are appendable; aliases are not,
        and aliasing a list forfeits the source's ownership too."""
        if isinstance(rhs_node, (ast.List, ast.ListComp)):
            self.owned.add(name)
            return
        self.owned.discard(name)
        if isinstance(rhs_node, ast.Name) and self._is_seqish(self._infer(rhs_node)):
            self.owned.discard(rhs_node.id)

    def _bool_ctx(self, test: ast.expr) -> str:
        """Encode an expression used as a condition; §7.3 truthiness for
        list/str operands."""
        if self._is_seqish(self._infer(test)):
            return f"(|{self.expr(test)}| != 0)"
        if _opt_inner(self._infer(test)) is not None:
            raise _err(test, (
                "truthiness on an Optional conflates None with falsy values "
                "(0, empty) — write `is None` / `is not None` explicitly"
            ))
        t = self._eff_type(test)
        if t is not None and t != "bool":
            raise _err(test, (
                f"truthiness on a {t}-typed value is outside the fragment — "
                f"write an explicit comparison (e.g. `x != 0`)"
            ))
        return self.expr(test)

    def _coerce(self, node: ast.expr, want: str | None) -> str:
        """Encode `node` where a value of type `want` is expected, injecting
        into / projecting out of PyOpt as Python's implicit union does. The
        `.v` projection carries a PySome? well-formedness VC — that is the
        catalog's 'narrowing replayed as VCs'."""
        if want is None:
            return self.expr(node)
        want_inner = _opt_inner(want)
        if want_inner is not None:
            if isinstance(node, ast.Constant) and node.value is None:
                return "PyNone"
            got = self._infer(node)
            if got == want:
                return self.expr(node)
            return f"PySome({self._coerce(node, want_inner)})"
        got = self._infer(node)
        if _opt_inner(got) == want:
            return f"({self.expr(node)}).v"
        return self.expr(node)

    def stmt(self, stmt: ast.stmt, indent: str) -> None:
        for clause in self._proofs_by_stmt.pop(id(stmt), []):
            self._emit_proof(clause, indent)
        match stmt:
            case ast.Expr(value=ast.Constant(value=str())):
                return  # docstring
            case ast.Pass():
                return
            case ast.Expr(value=ast.Call(
                func=ast.Attribute(value=ast.Name(id=target), attr="append"),
                args=[arg],
            )):
                if target in self.frozen:
                    raise _err(stmt, (
                        f"appending to {target!r} while iterating it — CPython's "
                        f"iterator would see the growth, the lowering's snapshot "
                        f"would not (§3.2: no mutation of an iterated container)"
                    ))
                if target not in self.owned:
                    raise _err(stmt, (
                        f"append target {target!r} is not a fresh, unaliased local "
                        f"list — the value lowering is sound only for owned "
                        f"containers (§3.2 ownership)"
                    ))
                mt = self._mangle(target)
                target_type = self.types.get(target)
                elem_type = target_type[4:-1] if target_type and target_type.startswith("seq<") else None
                self.emit(f"{indent}{mt} := {mt} + [{self._coerce(arg, elem_type)}];", stmt.lineno)
                return
            case ast.Expr(value=ast.Call(func=ast.Attribute(attr=method))):
                raise _err(stmt, f"method call .{method}(...) is outside the slice encoder")
            case ast.AnnAssign(target=ast.Name(id=name), annotation=ann, value=value) if value is not None:
                dtype = _dafny_type(ann, stmt)
                self._assign_name(name, self._coerce(value, dtype), indent, stmt, rhs_node=value, ann=dtype)
            case ast.Assign(targets=[ast.Name(id=name)], value=value):
                self._assign_name(
                    name,
                    self._coerce(value, self.types.get(name) or self.hoisted.get(name)),
                    indent, stmt, rhs_node=value,
                )
            case ast.Assign(targets=[ast.Tuple(elts=elts)], value=ast.Tuple(elts=values)) \
                    if len(elts) == len(values) and all(isinstance(e, ast.Name) for e in elts):
                names = [e.id for e in elts]  # type: ignore[union-attr]
                if len(set(names)) != len(names):
                    raise _err(stmt, "repeated names in tuple assignment are outside the fragment")
                for n in names:
                    if n in self.params:
                        raise _err(stmt, "parameter rebinding is outside the fragment (parameters are immutable)")
                    self.retired.discard(n)
                # Route every element through the same Optional injection/
                # projection coercion single assignments get.
                rhs = ", ".join(
                    self._coerce(v, self.types.get(n) or self.hoisted.get(n))
                    for n, v in zip(names, values)
                )
                lhs = ", ".join(self._mangle(n) for n in names)
                fresh = [n for n in names if not (self._declared(n) or n in self.hoisted)]
                if len(fresh) == len(names):
                    self.emit(f"{indent}var {lhs} := {rhs};", stmt.lineno)
                    for n, v in zip(names, values):
                        self._declare(n)
                        self.types.setdefault(n, self._infer(v))
                        self._update_ownership(n, v)
                elif not fresh:
                    self.emit(f"{indent}{lhs} := {rhs};", stmt.lineno)
                    for n, v in zip(names, values):
                        self._update_ownership(n, v)
                else:
                    raise _err(stmt, "tuple assignment mixing new and existing variables is outside the slice-1 encoder")
            case ast.AugAssign(target=ast.Name(id=name), op=op, value=value):
                if name in self.params:
                    raise _err(stmt, "parameter rebinding is outside the fragment (parameters are immutable)")
                if self.types.get(name) != "int" or self._infer(value) != "int":
                    raise _err(stmt, (
                        "augmented assignment on non-int operands is outside the "
                        "slice-1 encoder (Python's list `+=` mutates aliases in place)"
                    ))
                synthetic = ast.BinOp(left=ast.Name(id=name, ctx=ast.Load()), op=op, right=value)
                ast.copy_location(synthetic, stmt)
                ast.fix_missing_locations(synthetic)
                self.emit(f"{indent}{self._mangle(name)} := {self.expr(synthetic)};", stmt.lineno)
            case ast.Return(value=value):
                if value is None:
                    raise _err(stmt, "bare `return` is outside the slice-1 encoder")
                self.emit(f"{indent}result := {self._coerce(value, self.return_type)};", stmt.lineno)
                self.emit(f"{indent}return;")
            case ast.Assert(test=test, msg=msg):
                # Executable in CPython, a proof hint in Dafny — the same
                # dual role #@ specs have.
                if msg is not None and not isinstance(msg, ast.Constant):
                    raise _err(stmt, "assert messages must be literals (side effects)")
                self.emit(f"{indent}assert {self._bool_ctx(test)};", stmt.lineno)
            case ast.If(test=test, body=body, orelse=orelse):
                # Ownership is path-sensitive: a name is owned after the If
                # only if it is owned on EVERY path through it.
                pre_owned = set(self.owned)
                self.emit(f"{indent}if {self._bool_ctx(test)} {{", stmt.lineno)
                self.block(body, indent + "  ")
                then_owned = set(self.owned)
                if orelse:
                    self.owned = set(pre_owned)
                    self.emit(f"{indent}}} else {{")
                    self.block(orelse, indent + "  ")
                    else_owned = set(self.owned)
                else:
                    else_owned = pre_owned
                self.owned = then_owned & else_owned
                self.emit(f"{indent}}}")
            case ast.While(test=test, body=body, orelse=orelse):
                if orelse:
                    raise _err(stmt, "while/else is outside the fragment")
                pre_owned = set(self.owned)
                self.emit(f"{indent}while {self._bool_ctx(test)}", stmt.lineno)
                self._loop_clauses(stmt, indent)
                self.emit(f"{indent}{{")
                self.block(body, indent + "  ")
                self.emit(f"{indent}}}")
                # The body may run zero or many times: keep only names owned
                # both before the loop and at the end of its body.
                self.owned &= pre_owned
            case ast.For():
                it = stmt.iter
                if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) \
                        and it.func.id == "range":
                    self._for_range(stmt, indent)
                else:
                    self._for_each(stmt, indent)
            case _:
                raise _err(stmt, f"statement {type(stmt).__name__} is outside the slice-1 encoder")

    def _loop_clauses(self, loop: ast.While | ast.For, indent: str, extra: tuple[str, ...] = ()) -> None:
        for inv in extra:
            self.emit(f"{indent}  invariant {inv}")
        for clause in self._invariants_by_loop.get(id(loop), []):
            self.emit(f"{indent}  invariant {self.spec_expr(clause)}", clause.line)
        for clause in self._decreases_by_loop.get(id(loop), []):
            self.emit(f"{indent}  decreases {self.spec_expr(clause)}", clause.line)

    def _for_range(self, stmt: ast.For, indent: str) -> None:
        if stmt.orelse:
            raise _err(stmt, "for/else is outside the fragment")
        if not isinstance(stmt.target, ast.Name):
            raise _err(stmt, "only a simple index variable is supported in slice-1 `for`")
        it = stmt.iter
        if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
                and it.func.id == "range" and 1 <= len(it.args) <= 2
                and not it.keywords):
            raise _err(stmt, "only `for i in range(...)` (1-2 args) is in the slice-1 encoder")
        var = stmt.target.id
        if var in self.params:
            raise _err(stmt, "the loop index may not shadow a parameter (parameters are immutable)")
        for n in ast.walk(ast.Module(body=stmt.body, type_ignores=[])):
            if isinstance(n, (ast.Break, ast.Continue)):
                raise _err(n, "break/continue inside range-for is outside the slice-1 encoder")
            if isinstance(n, ast.Name) and n.id == var and isinstance(n.ctx, ast.Store):
                raise _err(n, "reassigning the loop index is outside the fragment")
        if len(it.args) == 1:
            lo_expr, hi_expr = "0", self.expr(it.args[0])
        else:
            lo_expr, hi_expr = self.expr(it.args[0]), self.expr(it.args[1])
        mv = self._mangle(var)
        pre_owned = set(self.owned)
        # Python evaluates range() bounds ONCE; hoist them. Fresh names are
        # made injective against every identifier in the function.
        lo = self._fresh(f"{mv}_lo")
        hi = self._fresh(f"{mv}_hi")
        self.emit(f"{indent}var {lo}, {hi} := {lo_expr}, {hi_expr};", stmt.lineno)
        self.retired.discard(var)
        if self._declared(var):
            self.emit(f"{indent}{mv} := {lo};", stmt.lineno)
        else:
            self.emit(f"{indent}var {mv} := {lo};", stmt.lineno)
            self._declare(var)
        self.types[var] = "int"
        if lo_expr == "0" or lo_expr.lstrip("(").rstrip(")").isdigit():
            self.nonneg.add(var)
        self.emit(f"{indent}while {mv} < {hi}", stmt.lineno)
        self._loop_clauses(stmt, indent, extra=(f"{lo} <= {mv} <= PyMax({lo}, {hi})",))
        self.emit(f"{indent}{{")
        self.block(stmt.body, indent + "  ")
        self.emit(f"{indent}  {mv} := {mv} + 1;")
        self.emit(f"{indent}}}")
        self.owned &= pre_owned
        self.nonneg.discard(var)
        # Python's index survives the loop with a DIFFERENT value than the
        # lowering's; retire it so later reads are rejected, not miscompiled.
        self.retired.add(var)

    def _for_each(self, stmt: ast.For, indent: str) -> None:
        """`for v in xs` over a list: snapshot the iterable (Python evaluates
        it once), drive a hidden index, bind the element per iteration."""
        if stmt.orelse:
            raise _err(stmt, "for/else is outside the fragment")
        if not isinstance(stmt.target, ast.Name):
            raise _err(stmt, "only a simple target variable is supported in for-each")
        it_type = self._infer(stmt.iter)
        if not (it_type is not None and it_type.startswith("seq<")):
            raise _err(stmt, "for-each iterables must be list-typed (or use `for i in range(...)`)")
        var = stmt.target.id
        if var in self.params:
            raise _err(stmt, "the loop target may not shadow a parameter (parameters are immutable)")
        if self._declared(var):
            raise _err(stmt, "the for-each target may not reuse an existing variable")
        for n in ast.walk(ast.Module(body=stmt.body, type_ignores=[])):
            if isinstance(n, (ast.Break, ast.Continue)):
                raise _err(n, "break/continue inside for-each is outside the slice encoder")
            if isinstance(n, ast.Name) and n.id == var and isinstance(n.ctx, ast.Store):
                raise _err(n, "reassigning the loop target is outside the fragment")
        for clause in self._invariants_by_loop.get(id(stmt), []):
            if clause.desugared:
                tree = ast.parse(clause.desugared, mode="eval")
                if any(isinstance(n, ast.Name) and n.id == var for n in ast.walk(tree)):
                    raise EncodeError(
                        f"the invariant references the for-each target {var!r}, which is "
                        f"not in scope at the loop head — rewrite the loop over "
                        f"`range(len(...))` to name the iteration state",
                        clause.line,
                    )
        snap = self._fresh(f"{self._mangle(var)}_it")
        idx = self._fresh(f"{self._mangle(var)}_i")
        self.emit(f"{indent}var {snap} := {self.expr(stmt.iter)};", stmt.lineno)
        self.emit(f"{indent}var {idx} := 0;", stmt.lineno)
        self.emit(f"{indent}while {idx} < |{snap}|", stmt.lineno)
        self._loop_clauses(stmt, indent, extra=(f"0 <= {idx} <= |{snap}|",))
        self.emit(f"{indent}{{")
        mv = self._mangle(var)
        self.emit(f"{indent}  var {mv} := {snap}[{idx}];", stmt.lineno)
        pre_owned = set(self.owned)
        # Freeze every list-typed name the iterable expression mentions — not
        # just a bare-Name iterable. `for v in (xs if flag else [2])` iterates
        # xs on one path, so xs must be unappendable for the loop's duration.
        # Only unfreeze what WE froze, so nested loops over the same list
        # cannot thaw an enclosing iteration.
        frozen_added: set[str] = set()
        for n in ast.walk(stmt.iter):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) \
                    and self._is_seqish(self.types.get(n.id)) \
                    and n.id not in self.frozen:
                frozen_added.add(n.id)
                self.frozen.add(n.id)
        self.scopes.append({var})
        self.types[var] = it_type[4:-1]
        try:
            for body_stmt in stmt.body:
                self.stmt(body_stmt, indent + "  ")
        finally:
            self.scopes.pop()
            self.frozen -= frozen_added
        self.owned &= pre_owned
        self.emit(f"{indent}  {idx} := {idx} + 1;")
        self.emit(f"{indent}}}")
        # The target's post-loop value differs between the languages (last
        # element vs out-of-scope); reject later reads.
        self.retired.add(var)

    # -- method -----------------------------------------------------------------------------------

    def encode(self) -> None:
        node = self.node
        a = node.args
        if a.vararg or a.kwarg or a.defaults or any(d is not None for d in a.kw_defaults):
            # NB: kw_defaults is [None, ...] for defaultless keyword-only
            # params — those are ordinary fragment parameters, not defaults.
            raise _err(node, "varargs/defaults are outside the fragment")
        for p in (*a.posonlyargs, *a.args, *a.kwonlyargs):
            self.types[p.arg] = _dafny_type(p.annotation, p)
        self.return_type = _dafny_type(node.returns, node)
        self.hoisted = self._hoist_analysis()
        params = ", ".join(
            f"{self._mangle(p.arg)}: {self.types[p.arg]}"
            for p in (*a.posonlyargs, *a.args, *a.kwonlyargs)
        )
        self.emit(f"method {self._mangle(node.name)}({params}) returns (result: {self.return_type})", node.lineno)
        for clause in self.spec.by_kind("requires"):
            self.emit(f"  requires {self.spec_expr(clause)}", clause.line)
        for clause in self.spec.by_kind("ensures"):
            self.emit(f"  ensures {self.spec_expr(clause)}", clause.line)
        self.emit("{")
        for name, dtype in self.hoisted.items():
            self.emit(f"  var {self._mangle(name)}: {dtype};", node.lineno)
            self.types.setdefault(name, dtype)
        self.scopes[-1].update()  # top scope: hoisted handled via self.hoisted
        self.block(node.body, "  ")
        self.emit("}")


@dataclass
class EncodedModule:
    dafny_source: str
    line_map: dict[int, int]  # 1-based dafny line -> python line
    methods: list[str]


def _module_shadow_check(module: ast.Module) -> None:
    """Reject module-level bindings of names the encoder resolves as
    builtins. An unspecced `def sum(...)` is not encoded, so every encoded
    call site would silently mean Python's builtin while CPython runs the
    user's definition — verified-but-false. Function bodies are scanned by
    _MethodEncoder for the functions that get encoded; module scope is the
    part no per-function check can see."""

    def check(name: str, line: int) -> None:
        if name in _ENCODED_BUILTINS:
            raise EncodeError(
                f"module-level binding of {name!r} shadows a builtin the "
                f"encoder gives meaning to — rename it", line)

    def scan(stmts: list[ast.stmt]) -> None:
        for stmt in stmts:
            match stmt:
                case ast.FunctionDef() | ast.AsyncFunctionDef() | ast.ClassDef():
                    check(stmt.name, stmt.lineno)  # do not descend
                    continue
                case ast.Import(names=aliases) | ast.ImportFrom(names=aliases):
                    for a in aliases:
                        check((a.asname or a.name).split(".")[0], stmt.lineno)
                case ast.For(body=body, orelse=orelse) \
                        | ast.While(body=body, orelse=orelse) \
                        | ast.If(body=body, orelse=orelse):
                    scan(body)
                    scan(orelse)
                case ast.With(body=body):
                    scan(body)
                case ast.Try(body=body, orelse=orelse, finalbody=finalbody,
                             handlers=handlers):
                    scan(body)
                    scan(orelse)
                    scan(finalbody)
                    for h in handlers:
                        if h.name:
                            check(h.name, h.lineno)
                        scan(h.body)
                case _:
                    pass
            # Assignment/loop/with targets and walrus expressions all bind
            # via Store-context Names; match patterns bind via name
            # attributes on the pattern nodes instead.
            for n in ast.walk(stmt):
                if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
                    check(n.id, n.lineno)
                elif isinstance(n, (ast.MatchAs, ast.MatchStar)) and n.name:
                    check(n.name, n.lineno)
                elif isinstance(n, ast.MatchMapping) and n.rest:
                    check(n.rest, n.lineno)

    scan(module.body)


def encode_module(
    source: str,
    specs: ModuleSpecs,
    module_name: str,
    proof_lemmas: frozenset[str] = frozenset(),
) -> EncodedModule:
    if specs.errors:
        first = specs.errors[0]
        raise EncodeError(f"spec error: {first.error}", first.line)
    module = ast.parse(source)
    _module_shadow_check(module)
    all_defs = [n for n in ast.walk(module) if isinstance(n, ast.FunctionDef)]
    seen_names: dict[str, int] = {}
    for fn in all_defs:
        if fn.name in seen_names:
            raise EncodeError(
                f"duplicate definition of {fn.name!r} (first at line {seen_names[fn.name]}) — "
                f"CPython runs the last def; the verifier would prove the first",
                fn.lineno,
            )
        seen_names[fn.name] = fn.lineno
    functions = {(n.name, n.lineno): n for n in all_defs}
    header = [
        f"// Generated by `lemmapy verify` -- DO NOT EDIT the stub (source: {module_name})",
        "// Proof additions belong below the STUB END marker (additions-only discipline).",
        "",
        *PREAMBLE.splitlines(),
        "",
    ]
    lines: list[str] = list(header)
    line_map: dict[int, int] = {}
    methods: list[str] = []
    for spec in specs.functions:
        node = functions.get((spec.name, spec.lineno))
        if node is None:
            raise EncodeError(f"cannot locate function {spec.name!r}", spec.lineno)
        enc = _MethodEncoder(node, spec, proof_lemmas, source_lines=source.split("\n"))
        enc.encode()
        offset = len(lines)
        lines.extend(enc.lines)
        lines.append("")
        for idx, py_line in enc.line_map.items():
            line_map[offset + idx + 1] = py_line  # 1-based dafny lines
        methods.append(spec.name)
    lines.append("// ---- STUB END: proof additions (lemmas, asserts) go below ----")
    return EncodedModule("\n".join(lines) + "\n", line_map, methods)
