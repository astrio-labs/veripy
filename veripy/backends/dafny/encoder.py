"""Clean-bucket fragment -> Dafny method stubs (the conformance authority).

`veripy check` dry-runs this encoder; a construct with no lowering is a
hard error, not a warning. There is no fragment IR — output is Dafny.

Scope (deliberately small; everything else is a detected, explained
rejection):
- types: int, bool, str, list[int|str|bool] (reads only: len, indexing —
  including negative indices, normalized Python-exactly via PyIndex),
  tuple[T, ...] of 2–8 fragment elements (Dafny `(T, U, …)`; index is a
  constant, unpacking is arity-checked)
- statements: assignment (incl. parallel tuple), if/elif/else, while,
  `for i in range(...)` (lowered to while with an auto bounds invariant),
  `for x in xs` (snapshot + hidden index; `for a, b in pairs` unpacks
  a `list[tuple[...]]` with an arity check), break/continue (continue on a
  desugared for emits the hidden-index step first — a bare Dafny
  `continue` would skip it and spin), return, assert
- expressions: arithmetic with PyFloorDiv/PyMod (INT operands only, except
  `+` which also concatenates two lists or two strs), comparisons
  (chained), and/or/not, len/min/max/abs, indexing, conditional expressions,
  single-generator list comprehensions (optional `if` filter via PyFlatten),
  eager `all`/`any`/`sum` genexp folds (filters included; all/any →
  forall/exists, sum → mapped PySum), `sorted(xs)` on `list[int]` as
  `PySorted` (permutation + order; no `key=`/`reverse=`/`list[str]`),
  walrus `:=` in always-evaluated
  positions (if/while tests, return, assignment, assert, call args;
  while-test `:=` is re-emitted at continue / loop-end — a bare Dafny
  `while` condition cannot assign), f-strings as concatenation of
  str pieces (no format spec, no `!s`/`!r`/`!a`, no int/bool/char
  interpolation — `str(int)` is a later row)
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
- Binary arithmetic operands are type-checked HERE, not left to Dafny:
  `s * 2`, `s % x`, `True + True` and `a - b` on strs all encoded to
  ill-typed Dafny and surfaced as a resolution error about `seq<char>`,
  which breaks the rule that this encoder is the conformance authority.
- One definition per function name per module: CPython runs the LAST def,
  the verifier would prove the first.
- `#@ invariant`/`#@ decreases` must sit at the top of the loop body,
  before its first statement (the documented convention, now enforced —
  trailing comment lines would otherwise attach to the wrong loop).
- Walrus `:=` under `and`/`or`, a later chained-comparison operand, a
  conditional-expression branch, or a comprehension is rejected: Dafny
  has no expression-level assignment, and hoisting those would ignore
  short-circuit / skip the bind.

Semantics note baked in here: `#@ invariant` has Dafny loop-head semantics
(holds on entry and at every head check, including the final one where the
guard is false). The range-for lowering auto-supplies the index bounds
invariant; range() bounds are hoisted because Python evaluates them once.

Output is a single self-contained .dfy stub (preamble inlined). Proof
additions live in a sibling `<stem>.proofs.dfy` sidecar, whitelist-
validated and concatenated after the STUB END marker. The repair loop
may edit the sidecar only.
"""

from __future__ import annotations

import ast
import copy
import re
from dataclasses import dataclass
from pathlib import Path

from ...frontend.parse import Clause, FunctionSpec, ModuleSpecs
from .preamble import PREAMBLE, PREAMBLE_NAMES


@dataclass(frozen=True)
class ProofSidecar:
    text: str
    lemmas: frozenset[str]
    # Where the pack came from, and how many lines `text` prepends before
    # the file's own line 1 — enough to map a stub line back to a location
    # a reader can OPEN. Derived from the wrapper, never a literal, so the
    # mapping follows if the wrapper changes.
    path: Path | None = None
    header_lines: int = 0

    @staticmethod
    def empty() -> "ProofSidecar":
        return ProofSidecar("", frozenset())

    def locate(self, dafny_line: int, stub_extent: int) -> tuple[str, int] | None:
        """(file, line) in the SIDECAR for a stub line, or None if that line
        is not in the sidecar region."""
        if self.path is None or dafny_line <= stub_extent:
            return None
        line = dafny_line - stub_extent - self.header_lines + 1
        return (str(self.path), line) if line >= 1 else None


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
    if token in (")", "]", ">", "|"):
        # `|` is the closing pipe of a cardinality — `decreases |s|` right
        # before a body is idiomatic Dafny. This admits no new masquerade:
        # a brace display ENDING a bodiless declaration after `|` cannot be
        # valid Dafny (`|expr|` must close its pipe, and the trailing `|`
        # after the display trips the declaration scan as a stray token).
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
        raise EncodeError(f"proof sidecar {name}: attributes ({{:...}}) are not allowed",
                          rule="attribute")
    if "@" in stripped:
        # Verbatim @-strings don't use backslash escapes and would evade the
        # string blanking above; nothing a lemma pack needs uses `@`.
        raise EncodeError(f"proof sidecar {name}: `@` is not allowed",
                          rule="forbidden-token")
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_']*|\{|\}|.", stripped)
    words = [t for t in tokens if t.strip()]
    for w in words:
        if w in _SIDECAR_FORBIDDEN:
            raise EncodeError(
                f"proof sidecar {name}: {w!r} is not allowed — sidecars may "
                f"contain only proved ghost declarations (lemma/function/predicate)",
                rule="forbidden-token",
            )
        if w == "~":
            raise EncodeError(f"proof sidecar {name}: partial-arrow types are not allowed",
                              rule="forbidden-token")
    for i in range(len(words) - 1):
        # An isolated `=>` is a lambda (its body brace follows a `>`, which
        # would defeat the value-ender body check); `==>` (implication) has a
        # preceding `=` and stays legal.
        if words[i] == "=" and words[i + 1] == ">" \
                and (i == 0 or words[i - 1] != "="):
            raise EncodeError(
                f"proof sidecar {name}: lambda expressions (`=>`) are not allowed",
                rule="lambda",
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
                        f"spec without set/map displays",
                        rule="spec-literal",
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
                    f"axiom — every lemma/function must be proved",
                    rule="bodiless",
                )
            if w == "ghost":
                if idx + 1 >= len(words) or words[idx + 1] not in ("function", "predicate"):
                    raise EncodeError(f"proof sidecar {name}: `ghost` must qualify function/predicate",
                                      rule="malformed-ghost")
                idx += 1
            if w == "lemma" and idx + 1 < len(words):
                lemmas.add(words[idx + 1])
            expecting_decl = False
            current_decl_has_body = False
        elif depth == 0 and expecting_decl:
            raise EncodeError(
                f"proof sidecar {name}: top-level {w!r} is not a ghost "
                f"declaration (lemma/function/predicate)",
                rule="non-declaration",
            )
        idx += 1
    if not current_decl_has_body:
        raise EncodeError(
            f"proof sidecar {name}: a declaration without a body is an axiom — "
            f"every lemma/function must be proved",
            rule="bodiless",
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
    header = f"\n// ---- proof additions from {sidecar.name} ----\n"
    return ProofSidecar(header + text, lemmas, path=sidecar,
                        header_lines=header.count("\n"))


def validate_sidecar_text(text: str, name: str) -> frozenset[str]:
    """Public entry to the sidecar whitelist: returns declared lemma names,
    raises EncodeError (with `.rule` set) on rejection. Used by the repair
    loop for proposal-time telemetry."""
    return _validate_sidecar(text, name)

DAFNY_KEYWORDS = frozenset({
    "method", "function", "lemma", "var", "ghost", "returns", "requires",
    "ensures", "invariant", "decreases", "reads", "modifies", "assert",
    "assume", "while", "forall", "exists", "match", "case", "int", "bool",
    "string", "seq", "set", "map", "old", "then", "print", "new", "this",
    "char", "nat", "real", "type", "datatype", "predicate", "true", "false",
})


class EncodeError(Exception):
    def __init__(self, message: str, line: int | None = None,
                 rule: str | None = None):
        super().__init__(message)
        self.message = message
        self.line = line
        # Machine-readable classification. ALWAYS set for encoder
        # rejections: an embedding host must route on a stable id, not on
        # English prose that is neither versioned nor documented.
        self.rule = rule


# Node class -> coarse rule id, used when a site does not name a finer one.
# Deriving a default means every rejection carries *some* stable id without
# 60-odd hand edits, and a caller can rely on the field being present.
_NODE_RULES: dict[type, str] = {
    ast.Assign: "unsupported-assignment",
    ast.AugAssign: "unsupported-assignment",
    ast.AnnAssign: "unsupported-assignment",
    ast.Call: "unsupported-call",
    ast.Attribute: "unsupported-attribute",
    ast.Subscript: "unsupported-subscript",
    ast.Compare: "unsupported-comparison",
    ast.BinOp: "unsupported-operator",
    ast.UnaryOp: "unsupported-operator",
    ast.BoolOp: "unsupported-operator",
    ast.For: "unsupported-loop",
    ast.While: "unsupported-loop",
    ast.Break: "unsupported-control-flow",
    ast.Continue: "unsupported-control-flow",
    ast.Try: "unsupported-control-flow",
    ast.Raise: "unsupported-control-flow",
    ast.Return: "unsupported-return",
    ast.Lambda: "unsupported-expression",
    ast.ListComp: "unsupported-comprehension",
    ast.SetComp: "unsupported-comprehension",
    ast.DictComp: "unsupported-comprehension",
    ast.GeneratorExp: "unsupported-comprehension",
    ast.JoinedStr: "unsupported-fstring",
    ast.FormattedValue: "unsupported-fstring",
    ast.ClassDef: "unsupported-class",
    ast.FunctionDef: "unsupported-function",
}


def _default_rule(node: ast.AST) -> str:
    for cls in type(node).__mro__:
        if cls in _NODE_RULES:
            return _NODE_RULES[cls]
    if isinstance(node, ast.stmt):
        return "unsupported-statement"
    if isinstance(node, ast.expr):
        return "unsupported-expression"
    return "unsupported-construct"


def _err(node: ast.AST, message: str, rule: str | None = None) -> EncodeError:
    return EncodeError(message, getattr(node, "lineno", None),
                       rule=rule or _default_rule(node))


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
        case ast.Subscript(value=ast.Name(id=("tuple" | "Tuple")), slice=sl):
            elts = sl.elts if isinstance(sl, ast.Tuple) else [sl]
            if not (2 <= len(elts) <= 8):
                raise _err(where, (
                    "tuple types in the fragment have 2–8 elements "
                    "(a 1-tuple is just the element; longer tuples are "
                    "outside the slice encoder)"
                ))
            parts = [_dafny_type(e, where) for e in elts]
            return "(" + ", ".join(parts) + ")"
        case ast.BinOp(left=left, op=ast.BitOr(), right=ast.Constant(value=None)):
            return f"PyOpt<{_dafny_type(left, where)}>"
        case ast.BinOp(left=ast.Constant(value=None), op=ast.BitOr(), right=right):
            return f"PyOpt<{_dafny_type(right, where)}>"
        case _:
            raise _err(where, f"type {ast.unparse(ann)!r} is outside the slice-1 encoder "
                       f"-- fragment types are int, bool, str, list[T], "
                       f"tuple[T, ...], and Optional[T] / T | None")


def _py_type_name(tdesc: str | None) -> str:
    """Dafny type descriptor -> the Python type the user wrote. Rejections
    must talk about the program, not about `seq<char>`."""
    if tdesc is None:
        return "an undetermined type"
    if tdesc in ("string", "char"):
        return "str"
    if tdesc.startswith("seq<"):
        return f"list[{_py_type_name(tdesc[4:-1])}]"
    if _is_tuple(tdesc):
        return "tuple[" + ", ".join(_py_type_name(p) for p in _tuple_elems(tdesc)) + "]"
    return tdesc


def _concat_types(left: ast.expr, right: ast.expr,
                  lt: str | None, rt: str | None) -> tuple[str | None, str | None]:
    """Operand types for `+`, with a bare `[]` typed by its sibling.

    An empty list literal has no element type of its own — which is why
    `x = []` demands an annotation — but in `[] + xs` the other operand
    supplies it, and that is exactly how Dafny types the `[] + xs` we emit.
    Without this the fail-closed operand check would reject a concatenation
    the fragment has always encoded and verified.

    Narrow on purpose: a literal `[]` only (not any untypeable operand),
    against a list only (`[] + "s"` is a TypeError in Python), and only
    for `+`. `[] + []` stays undecidable and stays rejected.
    """
    def bare_empty(n: ast.expr) -> bool:
        return isinstance(n, ast.List) and not n.elts

    if lt is None and bare_empty(left) and rt is not None and rt.startswith("seq<"):
        return rt, rt
    if rt is None and bare_empty(right) and lt is not None and lt.startswith("seq<"):
        return lt, lt
    return lt, rt


def _opt_inner(tdesc: str | None) -> str | None:
    """PyOpt<T> -> T, else None."""
    if tdesc is not None and tdesc.startswith("PyOpt<") and tdesc.endswith(">"):
        return tdesc[6:-1]
    return None


def _is_tuple(tdesc: str | None) -> bool:
    return bool(tdesc) and tdesc[0] == "(" and tdesc[-1] == ")"


def _tuple_elems(tdesc: str) -> list[str]:
    """Split a Dafny `(T, U, …)` descriptor, respecting nested tuples."""
    inner = tdesc[1:-1]
    parts: list[str] = []
    depth = 0
    start = 0
    for i, ch in enumerate(inner):
        if ch in "({<":
            depth += 1
        elif ch in ")}>":
            depth -= 1
        elif ch == "," and depth == 0:
            parts.append(inner[start:i].strip())
            start = i + 1
    parts.append(inner[start:].strip())
    return parts


def _const_int_index(node: ast.expr) -> int | None:
    """A constant tuple index, including the unary-minus form `p[-1]`."""
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        inner = _const_int_index(node.operand)
        if inner is not None:
            return -inner
    return None


_INT_SET = frozenset({"int"})
_ORDER_OK = frozenset({"int", "char"})


@dataclass
class _Scope:
    names: set[str]


_ENCODED_BUILTINS = frozenset({
    "len", "min", "max", "abs", "sum", "sorted", "range", "bool", "all", "any", "old",
})


def _preamble_clash(name: str) -> str | None:
    """The message for a Python name that lands on a preamble declaration,
    or None if it does not. Every encoded name shares one Dafny scope with
    the inlined preamble: a def becomes a duplicate top-level declaration,
    a local or binder shadows the function the encoder calls for `sum`,
    `%`, slicing and the rest. Both surface as a resolver error against
    generated Dafny that no Python line explains, so the encoder rejects
    the name in the fragment instead."""
    if name in PREAMBLE_NAMES:
        return (f"{name!r} collides with a declaration of the same name in "
                f"the Dafny preamble the stub inlines — rename it")
    return None


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
        for p in sorted(self.params & PREAMBLE_NAMES):
            raise EncodeError(f"parameter {_preamble_clash(p)}", node.lineno)
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
                clash = _preamble_clash(name)
                if clash:
                    raise _err(n, f"binding {clash}")
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
        # Innermost loop first. `continue` on a desugared for must run the
        # hidden-index step BEFORE Dafny's `continue`, or the loop spins
        # (the increment lives after the body in the while lowering).
        self._loops: list[tuple[str, ...]] = []

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
                if isinstance(op, ast.Add):
                    lt, rt = _concat_types(left, right, lt, rt)
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
            case ast.Call(func=ast.Name(id="sorted")):
                return "seq<int>"
            case ast.Call(func=ast.Name(id=("all" | "any"))):
                return "bool"
            case ast.Call(func=ast.Name(id="old"), args=[ast.Name(id=name)]):
                return self.types.get(name)
            case ast.Subscript(value=value, slice=ast.Slice()):
                return self._infer(value)  # a slice keeps the sequence type
            case ast.Subscript(value=value, slice=index):
                base = self._infer(value)
                if _is_tuple(base):
                    k = _const_int_index(index)
                    if k is None:
                        return None
                    elems = _tuple_elems(base)
                    if k < 0:
                        k += len(elems)
                    if 0 <= k < len(elems):
                        return elems[k]
                    return None
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
            case ast.Tuple(elts=elts):
                if any(isinstance(e, ast.Starred) for e in elts):
                    return None
                if not (2 <= len(elts) <= 8):
                    return None
                parts = [self._infer(e) for e in elts]
                if any(p is None for p in parts):
                    return None
                return "(" + ", ".join(parts) + ")"
            case ast.ListComp(elt=elt, generators=[comp]) if not comp.is_async:
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
            case ast.NamedExpr(value=value):
                return self._infer(value)
            case ast.JoinedStr():
                return "string" if self._joined_str_is_str(node) else None
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
                if type(op) not in self._ARITH_SYMBOL:
                    raise _err(node, f"operator {type(op).__name__} is outside the slice-1 encoder")
                # Operand types BEFORE emission: everything below assumes
                # them, and Dafny's own complaint arrives too late and in
                # the wrong vocabulary.
                self._check_arith(node, op, left, right)
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
                    case _:  # Pow
                        # Python int ** negative-int yields float -- outside
                        # the int fragment; PyPow's requires (e >= 0) is
                        # exactly that domain condition, replayed as a VC.
                        return f"PyPow({l}, {r})"
            case ast.Compare(left=left, ops=ops, comparators=comps):
                return self._compare(node, left, ops, comps)
            case ast.Call():
                return self._call(node)
            case ast.IfExp(test=test, body=body, orelse=orelse):
                return f"(if {self.expr(test)} then {self.expr(body)} else {self.expr(orelse)})"
            case ast.Subscript(value=value, slice=index):
                if isinstance(index, ast.Slice):
                    if _is_tuple(self._infer(value)):
                        raise _err(node, (
                            "slicing a tuple is outside the slice encoder — "
                            "index with a constant or unpack the components"
                        ))
                    if index.step is not None:
                        raise _err(node, "slice steps are outside the slice encoder")
                    base = self.expr(value)
                    lo = self.expr(index.lower) if index.lower is not None else "0"
                    hi = self.expr(index.upper) if index.upper is not None else f"|{base}|"
                    return f"PySlice({base}, {lo}, {hi})"
                if _is_tuple(self._infer(value)):
                    return self._tuple_index_expr(node, value, index)
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
            case ast.Tuple(elts=elts):
                if any(isinstance(e, ast.Starred) for e in elts):
                    raise _err(node, (
                        "starred tuple construction is outside the fragment — "
                        "write each component"
                    ))
                if not (2 <= len(elts) <= 8):
                    raise _err(node, (
                        "tuple literals in the fragment have 2–8 elements "
                        "(a 1-tuple is just the element; longer tuples are "
                        "outside the slice encoder)"
                    ))
                return "(" + ", ".join(self.expr(e) for e in elts) + ")"
            case ast.List(elts=elts):
                return "[" + ", ".join(self.expr(e) for e in elts) + "]"
            case ast.ListComp(elt=elt, generators=[comp]) if not comp.is_async \
                    and isinstance(comp.target, ast.Name):
                return self._list_comp(node, elt, comp)
            case ast.ListComp():
                raise _err(node, (
                    "only single-generator list comprehensions are in the "
                    "slice encoder (no nested `for`, no async) — bind "
                    "the inner sequence first, or write nested loops"
                ))
            case ast.NamedExpr():
                if self.spec_mode:
                    raise _err(node, (
                        "walrus `:=` in a spec clause has no assignment to "
                        "perform — write the condition without `:=`"
                    ))
                raise _err(node, (
                    "walrus `:=` in this position is outside this slice — "
                    "it is admitted in if/while tests, return, assignment, "
                    "assert, and always-evaluated call arguments; under "
                    "`and`/`or`, a chained comparison, or a comprehension "
                    "write an `if` or a loop"
                ))
            case ast.JoinedStr():
                return self._fstring(node)
            case _:
                raise _err(node, f"expression {type(node).__name__} is outside the slice-1 encoder "
                                 f"-- see the admitted-construct table in docs/SEMANTICS.md")

    def _tuple_index_expr(self, node: ast.Subscript, value: ast.expr,
                          index: ast.expr) -> str:
        """Project `p[k]` as Dafny `p.k`. The index is a constant (negative
        wrap is Python's); a variable index would treat a product as a
        sequence, which Dafny tuples are not."""
        elems = _tuple_elems(self._infer(value) or "")
        k = _const_int_index(index)
        if k is None:
            raise _err(node, (
                "tuple index must be a constant (Dafny tuples are product "
                "types, not sequences) — write `p[0]`/`p[1]` or unpack"
            ))
        n = len(elems)
        if k < 0:
            k += n
        if not (0 <= k < n):
            raise _err(node, (
                f"tuple index {ast.unparse(index)} is out of range for a "
                f"{n}-tuple (Python would raise IndexError) — the fragment "
                f"checks arity at encode time"
            ))
        base = self.expr(value)
        if not isinstance(value, ast.Name):
            base = f"({base})"
        return f"{base}.{k}"

    def _list_comp(self, node: ast.ListComp | ast.GeneratorExp, elt: ast.expr,
                   comp: ast.comprehension, require_int_elt: bool = False) -> str:
        raw = comp.target.id  # type: ignore[union-attr]
        if raw in self.params or self._declared(raw) \
                or raw in self.name_overrides or raw in self.types:
            raise _err(node, (
                f"comprehension binder {raw!r} shadows an existing name — "
                f"rename the binder"
            ))
        clash = _preamble_clash(raw)
        if clash:
            raise _err(node, f"comprehension binder {clash}")
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
            # Filters see the binder; Python evaluates each `if` in order
            # and skips the element when any is false.
            ifs = [self._bool_ctx(p) for p in comp.ifs]
        finally:
            if saved_override is None:
                self.name_overrides.pop(raw, None)
            else:
                self.name_overrides[raw] = saved_override
            if saved_type is None:
                self.types.pop(raw, None)
            else:
                self.types[raw] = saved_type
        seq_of = lambda body: (
            f"seq({count}, {idx} requires 0 <= {idx} < {count} => {body})"
        )
        if not ifs:
            return seq_of(body)
        pred = " && ".join(f"({p})" for p in ifs)
        if require_int_elt:
            # sum() of a filtered genexp: skipped elements contribute 0.
            return seq_of(f"(if {pred} then {body} else 0)")
        # [e for x in xs if P] → flatten a seq of 0/1-element seqs so
        # order is preserved and omitted elements do not leave a hole.
        return f"PyFlatten({seq_of(f'(if {pred} then [{body}] else [])')})"

    def _joined_str_is_str(self, node: ast.JoinedStr) -> bool:
        """True when every interpolation is a bare str (no spec, no
        conversion). Infer returns `string` only in that case so a
        rejected f-string does not type as str and then fail later."""
        for v in node.values:
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                continue
            if isinstance(v, ast.FormattedValue) and v.conversion == -1 \
                    and v.format_spec is None \
                    and self._infer(v.value) == "string":
                continue
            return False
        return True

    def _fstring(self, node: ast.JoinedStr) -> str:
        """`f"a{s}b"` → `"a" + s + "b"`. Identity on a str interpolation
        with no spec is CPython's default format; int/bool/char and
        format specs would need `str(int)` or the format mini-language,
        which are later rows."""
        parts: list[str] = []
        for v in node.values:
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                if v.value == "":
                    continue
                parts.append(self._escape_str(v.value, v))
                continue
            if not isinstance(v, ast.FormattedValue):
                raise _err(node, (
                    "f-string piece is outside the slice encoder — "
                    "interpolate a str value with no format spec"
                ))
            if v.conversion != -1:
                raise _err(v, (
                    "f-string conversions (`!s`/`!r`/`!a`) are outside "
                    "the slice encoder — interpolate a str value, or "
                    "write the concatenation explicitly (`a + b`)"
                ))
            if v.format_spec is not None:
                raise _err(v, (
                    "f-string format specs (`{x:...}`) are outside the "
                    "slice encoder — interpolate a str value with no "
                    "spec, or write the concatenation explicitly (`a + b`)"
                ))
            t = self._infer(v.value)
            if t != "string":
                raise _err(v, self._fstring_type_msg(t))
            parts.append(self.expr(v.value))
        if not parts:
            return '""'
        if len(parts) == 1:
            return parts[0]
        return "(" + " + ".join(parts) + ")"

    def _fstring_type_msg(self, t: str | None) -> str:
        if t == "int":
            return (
                "interpolating int in an f-string is outside this slice "
                "— `str(int)` is a later catalog row; concatenate str "
                "values, or write the digits as a literal"
            )
        if t == "bool":
            return (
                "interpolating bool in an f-string is outside this slice "
                "— Python would spell True/False; concatenate str values"
            )
        if t == "char":
            return (
                "interpolating a character (`s[i]`) is outside this "
                "slice — the model treats a str index as char, not str; "
                "slice `s[i:i+1]` instead"
            )
        if t is None:
            return (
                "cannot determine the type of an f-string interpolation; "
                "this slice interpolates str values only"
            )
        return (
            f"interpolating {_py_type_name(t)} in an f-string is outside "
            f"this slice — concatenate str values (`a + b`)"
        )

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

    # Python spelling for the operators the fragment models, so a rejection
    # talks about the user's program rather than about `seq<char>`.
    _ARITH_SYMBOL = {
        ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
        ast.FloorDiv: "//", ast.Mod: "%", ast.Pow: "**",
    }

    def _check_arith(self, node: ast.expr, op: ast.operator,
                     left: ast.expr, right: ast.expr) -> None:
        """Binary arithmetic is int-only, except `+` on two sequences.

        `check` is supposed to report exactly what `verify` would reject —
        the encoder dry-run IS the conformance authority (M1). It was not:
        `s * 2`, `a - b` on strs, `s % x` and `True + True` all passed
        `check` and then failed inside Dafny with a message about
        `seq<char>` at a line the reader has to map back by hand. An agent
        consuming the structured payload would get `resolution`, whose
        documented guidance ("the sidecar did not typecheck") points at the
        wrong file entirely.

        Fails closed, matching what `**` already did: an operand whose type
        the inferencer cannot determine is rejected rather than emitted and
        hoped for.
        """
        sym = self._ARITH_SYMBOL[type(op)]
        lt, rt = self._eff_type(left), self._eff_type(right)
        if isinstance(op, ast.Add):
            lt, rt = _concat_types(left, right, lt, rt)
        if lt == "int" and rt == "int":
            return
        if isinstance(op, ast.Add) and lt is not None and lt == rt \
                and self._is_seqish(lt):
            return  # concatenation: same meaning in both languages
        if isinstance(op, ast.Add) and _is_tuple(lt) and _is_tuple(rt):
            raise _err(node, (
                "tuple concatenation (`t + u`) is outside the slice encoder "
                "— Dafny tuples are product types, not sequences; construct "
                "a new tuple from the components"
            ))
        if isinstance(op, ast.Mult) and (
                (_is_tuple(lt) and rt == "int")
                or (lt == "int" and _is_tuple(rt))):
            raise _err(node, (
                "tuple repetition (`t * n`) is outside the slice encoder "
                "— Dafny tuples are product types with fixed arity"
            ))

        # Python DOES define these; they are simply not modeled yet. Say so,
        # rather than implying the program is wrong.
        if isinstance(op, ast.Mult) and (
                (self._is_seqish(lt) and rt == "int")
                or (lt == "int" and self._is_seqish(rt))):  # `3 * xs` too
            raise _err(node, (
                "sequence repetition (`s * n`) is outside the slice-1 "
                "encoder — build the value with a loop, or write the "
                "repeated literal"))
        if isinstance(op, ast.Mod) and lt == "string":
            raise _err(node, (
                "printf-style string formatting (`s % x`) is outside the "
                "slice-1 encoder — the fragment models `%` as integer "
                "modulo only"))
        if "bool" in (lt, rt):
            raise _err(node, (
                f"`{sym}` on a bool operand relies on Python's bool-to-int "
                f"coercion (`True + True == 2`), which is outside the "
                f"slice-1 encoder — write an explicit conditional"))
        if lt is None or rt is None:
            raise _err(node, (
                f"cannot determine the operand types of `{sym}`; the "
                f"fragment needs int operands (or two lists, or two strs, "
                f"for `+`)"))
        # Everything Python itself defines has been handled above, so what
        # is left is a TypeError in CPython. Say THAT: "outside the slice-1
        # encoder" would imply the fragment might grow to admit it.
        raise _err(node, (
            f"Python has no `{sym}` between {_py_type_name(lt)} and "
            f"{_py_type_name(rt)} (it raises TypeError) — in the fragment "
            f"arithmetic is int-only, and `+` additionally concatenates two "
            f"lists or two strs"))

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
                if _is_tuple(lt) or _is_tuple(rt):
                    raise _err(node, (
                        "order comparison on tuples is outside the slice "
                        "encoder — Dafny's tuple ordering is not Python's "
                        "lexicographic order"
                    ))
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
            raise _err(node, "method calls are outside the slice-1 encoder -- only "
                             "`xs.append(v)` statements are modeled")
        name = func.id
        args = node.args
        if name == "sorted":
            # One positional list[int]; key=/reverse=/str stay rejected
            # with a rewrite (Dafny seq < is prefix, not lex).
            if node.keywords or len(args) != 1 \
                    or self._infer(args[0]) != "seq<int>":
                raise _err(node, (
                    "sorted() in this slice takes a list[int] — drop "
                    "key=/reverse=, or sort a list of ints; for strings "
                    "write an explicit loop (Dafny seq order is prefix, "
                    "not lex)"
                ))
            return f"PySorted({self.expr(args[0])})"
        if node.keywords:
            # No encoded builtin takes keywords; silently dropping one
            # (e.g. max(a, b, key=abs)) would change the meaning.
            raise _err(node, f"keyword arguments to {name}() are outside the fragment")
        if name == "len" and len(args) == 1:
            t = self._infer(args[0])
            if _is_tuple(t):
                # Dafny `|p|` is sequence length; a tuple's len is its
                # (static) arity. Fragment expressions are pure, so
                # emitting the constant does not drop observable effects.
                return str(len(_tuple_elems(t)))
            return f"|{self.expr(args[0])}|"
        if name == "tuple":
            raise _err(node, (
                "tuple() conversion is outside the slice encoder — write "
                "a tuple literal `(a, b)`"
            ))
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
                if len(arg.generators) != 1 \
                        or arg.generators[0].is_async \
                        or not isinstance(arg.generators[0].target, ast.Name):
                    raise _err(node, (
                        "sum() accepts only single-generator, non-async "
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
        if name in ("all", "any") and len(args) == 1 \
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
                clash = _preamble_clash(raw)
                if clash:
                    raise _err(gen, f"quantifier binder {clash}")
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
                for pred in comp.ifs:
                    domains.append(self._bool_ctx(pred))
            body = self.expr(gen.elt)
            if not self.spec_mode and self._eff_type(gen.elt) != "bool":
                raise _err(gen, (
                    f"{kind}() needs a bool-valued generator expression — "
                    "write an explicit comparison (e.g. `x > 0`)"
                ))
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

        def record_expr_loads(node: ast.AST, path: tuple, stmt: ast.stmt) -> None:
            for n in ast.walk(node):
                if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                    loads.setdefault(n.id, []).append(path)
                elif isinstance(n, ast.NamedExpr) and isinstance(n.target, ast.Name):
                    record_store(n.target.id, path, n.value, stmt)

        def walk(stmts: list[ast.stmt], path: tuple) -> None:
            for idx, stmt in enumerate(stmts):
                match stmt:
                    case ast.Assign(targets=[ast.Name(id=name)], value=value):
                        record_store(name, path, value, stmt)
                        record_expr_loads(value, path, stmt)
                    case ast.Assign(targets=[ast.Tuple(elts=elts)], value=value):
                        if isinstance(value, ast.Tuple):
                            vals = value.elts
                            for j, e in enumerate(elts):
                                if isinstance(e, ast.Name):
                                    record_store(
                                        e.id, path,
                                        vals[j] if j < len(vals) else None,
                                        stmt,
                                    )
                        else:
                            vt = self._infer(value)
                            elems = _tuple_elems(vt) if _is_tuple(vt) else []
                            for j, e in enumerate(elts):
                                if isinstance(e, ast.Name):
                                    record_store(e.id, path, None, stmt)
                                    if j < len(elems) and e.id not in ann_types:
                                        ann_types[e.id] = elems[j]
                        record_expr_loads(value, path, stmt)
                    case ast.AnnAssign(target=ast.Name(id=name), annotation=ann, value=value):
                        record_store(name, path, value, stmt)
                        try:
                            ann_types[name] = _dafny_type(ann, stmt)
                        except EncodeError:
                            pass
                        if value is not None:
                            record_expr_loads(value, path, stmt)
                    case ast.AugAssign(target=ast.Name(id=name), value=value):
                        record_store(name, path, None, stmt)
                        loads.setdefault(name, []).append(path)
                        record_expr_loads(value, path, stmt)
                    case ast.If(test=test, body=body, orelse=orelse):
                        record_expr_loads(test, path, stmt)
                        walk(body, path + (idx, "t"))
                        walk(orelse, path + (idx, "e"))
                    case ast.While(test=test, body=body):
                        record_expr_loads(test, path, stmt)
                        walk(body, path + (idx, "w"))
                    case ast.For(target=target, iter=it, body=body):
                        for n in ast.walk(target):
                            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
                                loop_indices.add(n.id)
                        record_expr_loads(it, path, stmt)
                        walk(body, path + (idx, "f"))
                    case _:
                        record_expr_loads(stmt, path, stmt)

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

    def _assign_unpack(self, stmt: ast.Assign, elts: list[ast.expr],
                       value: ast.expr, indent: str) -> None:
        """Parallel `a, b = x, y` or unpack `a, b = p` from a tuple-typed
        RHS. Dafny rejects `a, b := p` (one RHS), so a tuple-typed name
        projects as `a, b := p.0, p.1`. A complex RHS is bound once so
        the projections do not double-evaluate it."""
        if any(isinstance(e, ast.Starred) for e in elts):
            raise _err(stmt, (
                "starred unpacking is outside the fragment — name each "
                "component"
            ))
        if not all(isinstance(e, ast.Name) for e in elts):
            raise _err(stmt, "unpacking targets must be plain names")
        names = [e.id for e in elts]  # type: ignore[union-attr]
        if len(set(names)) != len(names):
            raise _err(stmt, "repeated names in tuple assignment are outside the fragment")
        for n in names:
            if n in self.params:
                raise _err(stmt, "parameter rebinding is outside the fragment (parameters are immutable)")
            self.retired.discard(n)

        if isinstance(value, ast.Tuple):
            if any(isinstance(e, ast.Starred) for e in value.elts):
                raise _err(stmt, (
                    "starred tuple construction is outside the fragment — "
                    "write each component"
                ))
            if len(value.elts) != len(names):
                raise _err(stmt, (
                    f"unpacking expects {len(names)} values, got "
                    f"{len(value.elts)} (Python would raise ValueError)"
                ))
            rhs = ", ".join(
                self._coerce(v, self.types.get(n) or self.hoisted.get(n))
                for n, v in zip(names, value.elts)
            )
            rhs_types = [self._infer(v) for v in value.elts]
            rhs_nodes: list[ast.expr | None] = list(value.elts)
        else:
            got = self._infer(value)
            if not _is_tuple(got):
                raise _err(stmt, (
                    "unpacking a non-tuple is outside the fragment — only "
                    "a tuple-typed name or a tuple literal `(a, b)`"
                ))
            elems = _tuple_elems(got)
            if len(elems) != len(names):
                raise _err(stmt, (
                    f"unpacking expects {len(names)} values, got a tuple "
                    f"of arity {len(elems)} (Python would raise ValueError)"
                ))
            if isinstance(value, ast.Name):
                base = self._mangle(value.id)
            else:
                tmp = self._fresh("tup")
                self.emit(f"{indent}var {tmp} := {self.expr(value)};", stmt.lineno)
                base = tmp
            rhs = ", ".join(f"{base}.{i}" for i in range(len(names)))
            rhs_types = elems
            rhs_nodes = [None] * len(names)

        lhs = ", ".join(self._mangle(n) for n in names)
        fresh = [n for n in names if not (self._declared(n) or n in self.hoisted)]
        if len(fresh) == len(names):
            self.emit(f"{indent}var {lhs} := {rhs};", stmt.lineno)
            for n, t, v in zip(names, rhs_types, rhs_nodes):
                self._declare(n)
                self.types.setdefault(n, t)
                self._update_ownership(n, v)
        elif not fresh:
            self.emit(f"{indent}{lhs} := {rhs};", stmt.lineno)
            for n, v in zip(names, rhs_nodes):
                self._update_ownership(n, v)
        else:
            raise _err(stmt, "tuple assignment mixing new and existing variables is outside the slice-1 encoder")

    def _update_ownership(self, name: str, rhs_node: ast.expr | None) -> None:
        """Ownership-lite: fresh allocations are appendable; aliases are not,
        and aliasing a list forfeits the source's ownership too."""
        if isinstance(rhs_node, (ast.List, ast.ListComp)):
            self.owned.add(name)
            return
        self.owned.discard(name)
        if isinstance(rhs_node, ast.Name) and self._is_seqish(self._infer(rhs_node)):
            self.owned.discard(rhs_node.id)

    def _reject_walrus_context(self, expr: ast.expr) -> None:
        """Refuse `:=` that would not always run, or that has no assignment
        in a spec. Dafny cannot spell expression-level assignment, so
        hoisting those would ignore short-circuit."""
        encoder = self

        class _Walk(ast.NodeVisitor):
            def __init__(self) -> None:
                self.lazy = 0
                self.nested = 0

            def visit_NamedExpr(self, node: ast.NamedExpr) -> None:
                if encoder.spec_mode:
                    raise _err(node, (
                        "walrus `:=` in a spec clause has no assignment to "
                        "perform — write the condition without `:=`"
                    ))
                if self.nested:
                    raise _err(node, (
                        "walrus in a comprehension or lambda is outside this "
                        "slice — Python binds it in the enclosing scope; "
                        "write a loop"
                    ))
                if self.lazy:
                    raise _err(node, (
                        "walrus under `and`/`or`, a chained comparison, or "
                        "a conditional expression is outside this slice — "
                        "short-circuit would skip the assignment; write an "
                        "`if`"
                    ))
                if not isinstance(node.target, ast.Name):
                    raise _err(node, "walrus target must be a plain name")
                self.visit(node.value)

            def visit_BoolOp(self, node: ast.BoolOp) -> None:
                self.lazy += 1
                self.generic_visit(node)
                self.lazy -= 1

            def visit_IfExp(self, node: ast.IfExp) -> None:
                self.visit(node.test)
                self.lazy += 1
                self.visit(node.body)
                self.visit(node.orelse)
                self.lazy -= 1

            def visit_Compare(self, node: ast.Compare) -> None:
                # `a < b < c` evaluates `c` only if `a < b` is true.
                # `left` and the first comparator always run.
                self.visit(node.left)
                if node.comparators:
                    self.visit(node.comparators[0])
                    self.lazy += 1
                    for later in node.comparators[1:]:
                        self.visit(later)
                    self.lazy -= 1

            def visit_ListComp(self, node: ast.ListComp) -> None:
                self.nested += 1
                self.generic_visit(node)
                self.nested -= 1

            visit_SetComp = visit_ListComp
            visit_DictComp = visit_ListComp
            visit_GeneratorExp = visit_ListComp
            visit_Lambda = visit_ListComp

        _Walk().visit(expr)

    def _strip_walruses(self, expr: ast.expr) -> tuple[ast.expr, list[ast.NamedExpr]]:
        if not any(isinstance(n, ast.NamedExpr) for n in ast.walk(expr)):
            return expr, []
        bindings: list[ast.NamedExpr] = []

        class _Strip(ast.NodeTransformer):
            def visit_NamedExpr(self, node: ast.NamedExpr) -> ast.expr:
                value = self.visit(node.value)
                bound = ast.NamedExpr(target=node.target, value=value)
                ast.copy_location(bound, node)
                bindings.append(bound)
                if not isinstance(node.target, ast.Name):
                    return node
                return ast.copy_location(
                    ast.Name(id=node.target.id, ctx=ast.Load()), node)

        stripped = _Strip().visit(copy.deepcopy(expr))
        ast.fix_missing_locations(stripped)
        return stripped, bindings

    def _emit_walrus_bindings(self, bindings: list[ast.NamedExpr],
                              indent: str, stmt: ast.stmt) -> None:
        for ne in bindings:
            if not isinstance(ne.target, ast.Name):
                raise _err(stmt, "walrus target must be a plain name")
            name = ne.target.id
            expected = self.types.get(name) or self.hoisted.get(name)
            self._assign_name(
                name, self._coerce(ne.value, expected), indent, stmt,
                rhs_node=ne.value,
            )

    def _walrus_rebind_steps(self, bindings: list[ast.NamedExpr]) -> tuple[str, ...]:
        steps: list[str] = []
        for ne in bindings:
            if not isinstance(ne.target, ast.Name):
                continue
            name = ne.target.id
            expected = self.types.get(name) or self.hoisted.get(name)
            rhs = self._coerce(ne.value, expected)
            steps.append(f"{self._mangle(name)} := {rhs};")
        return tuple(steps)

    def _emit_walruses(self, expr: ast.expr, indent: str, stmt: ast.stmt) -> ast.expr:
        """Turn always-evaluated `:=` into assignments; return the
        assignment-free expression (the bound names)."""
        self._reject_walrus_context(expr)
        stripped, bindings = self._strip_walruses(expr)
        self._emit_walrus_bindings(bindings, indent, stmt)
        return stripped

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
            case ast.Expr(value=ast.NamedExpr() as value):
                self._emit_walruses(value, indent, stmt)
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
                arg = self._emit_walruses(arg, indent, stmt)
                mt = self._mangle(target)
                target_type = self.types.get(target)
                elem_type = target_type[4:-1] if target_type and target_type.startswith("seq<") else None
                self.emit(f"{indent}{mt} := {mt} + [{self._coerce(arg, elem_type)}];", stmt.lineno)
                return
            case ast.Expr(value=ast.Call(func=ast.Attribute(attr=method))):
                raise _err(stmt, f"method call .{method}(...) is outside the slice encoder")
            case ast.AnnAssign(target=ast.Name(id=name), annotation=ann, value=value) if value is not None:
                value = self._emit_walruses(value, indent, stmt)
                dtype = _dafny_type(ann, stmt)
                self._assign_name(name, self._coerce(value, dtype), indent, stmt, rhs_node=value, ann=dtype)
            case ast.Assign(targets=[ast.Name(id=name)], value=value):
                value = self._emit_walruses(value, indent, stmt)
                self._assign_name(
                    name,
                    self._coerce(value, self.types.get(name) or self.hoisted.get(name)),
                    indent, stmt, rhs_node=value,
                )
            case ast.Assign(targets=[ast.Tuple(elts=elts)], value=value):
                value = self._emit_walruses(value, indent, stmt)
                self._assign_unpack(stmt, elts, value, indent)
            case ast.AugAssign(target=ast.Name(id=name), op=op, value=value):
                if name in self.params:
                    raise _err(stmt, "parameter rebinding is outside the fragment (parameters are immutable)")
                value = self._emit_walruses(value, indent, stmt)
                if self.types.get(name) != "int" or self._infer(value) != "int":
                    raise _err(stmt, (
                        "augmented assignment on non-int operands is outside the "
                        "slice-1 encoder (Python's list `+=` mutates aliases in place)"
                    ))
                synthetic = ast.BinOp(left=ast.Name(id=name, ctx=ast.Load()), op=op, right=value)
                ast.copy_location(synthetic, stmt)
                ast.fix_missing_locations(synthetic)
                self.emit(f"{indent}{self._mangle(name)} := {self.expr(synthetic)};", stmt.lineno)
            case ast.Break():
                if not self._loops:
                    raise _err(stmt, "`break` is only meaningful inside a loop")
                self.emit(f"{indent}break;", stmt.lineno)
            case ast.Continue():
                if not self._loops:
                    raise _err(stmt, "`continue` is only meaningful inside a loop")
                for step in self._loops[-1]:
                    self.emit(f"{indent}{step}", stmt.lineno)
                self.emit(f"{indent}continue;", stmt.lineno)
            case ast.Return(value=value):
                if value is None:
                    raise _err(stmt, "bare `return` is outside the slice-1 encoder")
                value = self._emit_walruses(value, indent, stmt)
                self.emit(f"{indent}result := {self._coerce(value, self.return_type)};", stmt.lineno)
                self.emit(f"{indent}return;")
            case ast.Assert(test=test, msg=msg):
                # Executable in CPython, a proof hint in Dafny — the same
                # dual role #@ specs have.
                if msg is not None and not isinstance(msg, ast.Constant):
                    raise _err(stmt, "assert messages must be literals (side effects)")
                test = self._emit_walruses(test, indent, stmt)
                self.emit(f"{indent}assert {self._bool_ctx(test)};", stmt.lineno)
            case ast.If(test=test, body=body, orelse=orelse):
                # Ownership is path-sensitive: a name is owned after the If
                # only if it is owned on EVERY path through it.
                pre_owned = set(self.owned)
                test = self._emit_walruses(test, indent, stmt)
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
                # The while condition runs every head check, including after
                # continue. Hoist `:=` before the loop and re-emit the same
                # assignments at continue / fall-through — a Dafny `while`
                # test cannot assign.
                self._reject_walrus_context(test)
                test, bindings = self._strip_walruses(test)
                self._emit_walrus_bindings(bindings, indent, stmt)
                self.emit(f"{indent}while {self._bool_ctx(test)}", stmt.lineno)
                self._loop_clauses(stmt, indent)
                self.emit(f"{indent}{{")
                steps = self._walrus_rebind_steps(bindings)
                self._loops.append(steps)
                self.block(body, indent + "  ")
                for step in steps:
                    self.emit(f"{indent}  {step}", stmt.lineno)
                self._loops.pop()
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
            case ast.Assign(targets=[ast.Subscript()]):
                # Reached only because the supported Assign shapes did not
                # match. Saying "Assign is unsupported" while listing
                # assignment as admitted is what a repair agent loops on.
                raise _err(stmt,
                           "indexed assignment (`xs[i] = ...`) is outside the "
                           "slice-1 encoder -- rebuild the list instead (e.g. "
                           "a comprehension or append); see docs/SEMANTICS.md",
                           rule="indexed-assignment")
            case ast.Assign(targets=[ast.Attribute()]):
                raise _err(stmt,
                           "attribute assignment (`obj.field = ...`) is outside "
                           "the slice-1 encoder -- the fragment has value "
                           "semantics and no object mutation",
                           rule="attribute-assignment")
            case ast.Assign(targets=targets) if len(targets) > 1:
                raise _err(stmt,
                           "chained assignment (`a = b = ...`) is outside the "
                           "slice-1 encoder -- assign one target at a time",
                           rule="chained-assignment")
            case ast.Assign():
                raise _err(stmt,
                           "this assignment form is outside the slice-1 "
                           "encoder -- admitted targets: a single name, or a "
                           "tuple of names for a parallel swap, or unpacking "
                           "a tuple-typed value",
                           rule="unsupported-assignment")
            case _:
                raise _err(stmt, f"statement {type(stmt).__name__} is outside the slice-1 encoder "
                                 f"-- admitted: assignment, if/else, while, for over "
                                 f"range/list, break, continue, assert, return, append; "
                                 f"see docs/SEMANTICS.md")

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
            if isinstance(n, ast.Name) and n.id == var and isinstance(n.ctx, ast.Store):
                raise _err(n, "reassigning the loop index is outside the fragment")
        range_args = [self._emit_walruses(a, indent, stmt) for a in it.args]
        if len(range_args) == 1:
            lo_expr, hi_expr = "0", self.expr(range_args[0])
        else:
            lo_expr, hi_expr = self.expr(range_args[0]), self.expr(range_args[1])
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
        self._loops.append((f"{mv} := {mv} + 1;",))
        self.block(stmt.body, indent + "  ")
        self._loops.pop()
        self.emit(f"{indent}  {mv} := {mv} + 1;")
        self.emit(f"{indent}}}")
        self.owned &= pre_owned
        self.nonneg.discard(var)
        # Python's index survives the loop with a DIFFERENT value than the
        # lowering's; retire it so later reads are rejected, not miscompiled.
        self.retired.add(var)

    def _for_each(self, stmt: ast.For, indent: str) -> None:
        """`for v in xs` over a list: snapshot the iterable (Python evaluates
        it once), drive a hidden index, bind the element per iteration.
        `for a, b in pairs` over `list[tuple[T, U]]` projects `snap[i].0`,
        `snap[i].1` — the same unpacking Dafny cannot spell as `a, b := p`."""
        if stmt.orelse:
            raise _err(stmt, "for/else is outside the fragment")
        names = self._for_each_names(stmt)
        it = self._emit_walruses(stmt.iter, indent, stmt)
        it_type = self._infer(it)
        if not (it_type is not None and it_type.startswith("seq<")):
            raise _err(stmt, "for-each iterables must be list-typed (or use `for i in range(...)`)")
        elem = it_type[4:-1]
        if len(names) > 1:
            if not _is_tuple(elem):
                raise _err(stmt, (
                    "destructuring `for a, b in xs` needs a list of tuples "
                    "— iterate a `list[tuple[...]]`, or use a single target"
                ))
            elems = _tuple_elems(elem)
            if len(elems) != len(names):
                raise _err(stmt, (
                    f"for-each unpacking expects {len(names)} values, got "
                    f"a tuple of arity {len(elems)} (Python would raise "
                    f"ValueError)"
                ))
            bind_types = elems
        else:
            bind_types = [elem]
        for var in names:
            if var in self.params:
                raise _err(stmt, "the loop target may not shadow a parameter (parameters are immutable)")
            if self._declared(var):
                raise _err(stmt, "the for-each target may not reuse an existing variable")
        for n in ast.walk(ast.Module(body=stmt.body, type_ignores=[])):
            if isinstance(n, ast.Name) and n.id in names and isinstance(n.ctx, ast.Store):
                raise _err(n, "reassigning the loop target is outside the fragment")
        for clause in self._invariants_by_loop.get(id(stmt), []):
            if clause.desugared:
                tree = ast.parse(clause.desugared, mode="eval")
                hit = next((v for v in names
                            if any(isinstance(n, ast.Name) and n.id == v
                                   for n in ast.walk(tree))), None)
                if hit is not None:
                    raise EncodeError(
                        f"the invariant references the for-each target {hit!r}, which is "
                        f"not in scope at the loop head — rewrite the loop over "
                        f"`range(len(...))` to name the iteration state",
                        clause.line,
                    )
        head = self._mangle(names[0])
        snap = self._fresh(f"{head}_it")
        idx = self._fresh(f"{head}_i")
        self.emit(f"{indent}var {snap} := {self.expr(it)};", stmt.lineno)
        self.emit(f"{indent}var {idx} := 0;", stmt.lineno)
        self.emit(f"{indent}while {idx} < |{snap}|", stmt.lineno)
        self._loop_clauses(stmt, indent, extra=(f"0 <= {idx} <= |{snap}|",))
        self.emit(f"{indent}{{")
        if len(names) == 1:
            mv = self._mangle(names[0])
            self.emit(f"{indent}  var {mv} := {snap}[{idx}];", stmt.lineno)
        else:
            lhs = ", ".join(self._mangle(n) for n in names)
            rhs = ", ".join(f"{snap}[{idx}].{i}" for i in range(len(names)))
            self.emit(f"{indent}  var {lhs} := {rhs};", stmt.lineno)
        pre_owned = set(self.owned)
        # Freeze every list-typed name the iterable expression mentions — not
        # just a bare-Name iterable. `for v in (xs if flag else [2])` iterates
        # xs on one path, so xs must be unappendable for the loop's duration.
        # Only unfreeze what WE froze, so nested loops over the same list
        # cannot thaw an enclosing iteration.
        frozen_added: set[str] = set()
        for n in ast.walk(it):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) \
                    and self._is_seqish(self.types.get(n.id)) \
                    and n.id not in self.frozen:
                frozen_added.add(n.id)
                self.frozen.add(n.id)
        self.scopes.append(set(names))
        for var, t in zip(names, bind_types):
            self.types[var] = t
        self._loops.append((f"{idx} := {idx} + 1;",))
        try:
            for body_stmt in stmt.body:
                self.stmt(body_stmt, indent + "  ")
        finally:
            self._loops.pop()
            self.scopes.pop()
            self.frozen -= frozen_added
        self.owned &= pre_owned
        self.emit(f"{indent}  {idx} := {idx} + 1;")
        self.emit(f"{indent}}}")
        # The target's post-loop value differs between the languages (last
        # element vs out-of-scope); reject later reads.
        self.retired.update(names)

    def _for_each_names(self, stmt: ast.For) -> list[str]:
        t = stmt.target
        if isinstance(t, ast.Name):
            return [t.id]
        if isinstance(t, ast.Tuple):
            if any(isinstance(e, ast.Starred) for e in t.elts):
                raise _err(stmt, (
                    "starred for-each unpacking is outside the fragment — "
                    "name each component"
                ))
            if not all(isinstance(e, ast.Name) for e in t.elts):
                raise _err(stmt, "for-each unpacking targets must be plain names")
            names = [e.id for e in t.elts]  # type: ignore[union-attr]
            if len(set(names)) != len(names):
                raise _err(stmt, "repeated names in for-each unpacking are outside the fragment")
            if not (2 <= len(names) <= 8):
                raise _err(stmt, (
                    "for-each unpacking in the fragment has 2–8 names "
                    "(matching tuple arity)"
                ))
            return names
        raise _err(stmt, (
            "only a simple target, or a tuple of names unpacking a "
            "list of tuples, is supported in for-each"
        ))

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
        clash = _preamble_clash(name)
        if clash:
            raise EncodeError(f"module-level binding of {clash}", line)

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
    top_level = {(n.name, n.lineno) for n in module.body if isinstance(n, ast.FunctionDef)}
    for spec in specs.functions:
        if (spec.name, spec.lineno) in functions and (spec.name, spec.lineno) not in top_level:
            raise EncodeError(
                f"{spec.name!r} is a nested function — only module-level "
                f"functions are in the fragment (a closure's environment "
                f"has no Dafny model)", spec.lineno)
    header = [
        f"// Generated by `veripy verify` -- DO NOT EDIT the stub (source: {module_name})",
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
