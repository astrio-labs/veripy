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
  forall/exists, sum → mapped PySum), imported `math.gcd` / `factorial` /
  `isqrt` (`PyGcd`/`PyFact`/`PyIsqrt`; IEEE float is a permanent veto),
  `sorted(xs)` on integer lists or lists of integer pairs/triples as
  `PySorted`/`PySorted2`/`PySorted3` (no general `key=`/`reverse=`/`list[str]`),
  walrus `:=` in always-evaluated
  positions (if/while tests, return, assignment, assert, call args;
  while-test `:=` is re-emitted at continue / loop-end — a bare Dafny
  `while` condition cannot assign), f-strings as concatenation of
  str pieces (no format spec, no `!s`/`!r`/`!a`, no int/bool/char
  interpolation — write `str(n)` for int-to-str), `str(n)` via
  PyIntToStr (int operand only; bool is a disjoint sort), `int(s)`
  via PyStrToInt (str operand; requires PyIsIntStr is the parse VC),
  str methods on a str receiver: `sep.join(xs)`, `s.split(sep)`
  (nonempty sep, unlimited), `s.find(sub)`, `s.startswith`/`endswith`
  (one str, not a tuple), `s.replace(old, new)` (nonempty old, no
  count), `s.strip(chars)` / `lstrip` / `rstrip` (chars required).
  Unicode-table methods (`lower`/`upper`/`isdigit`/…) and no-arg
  `strip`/`split` are rejected — ASCII-only would be a silent
  approximation.
- calls: closed same-module acyclic scalar/Optional helper calls, checked
  bodies and contracts, eager expression temporaries, Python argument binding;
  conditional-expression and loop-header call contexts remain rejected.
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
from dataclasses import dataclass, field
from pathlib import Path

from veripy.frontend.parse import Clause, FunctionSpec, ModuleSpecs
from veripy.frontend.records import RecordError, record_schemas, record_type, record_constructor, record_field
from veripy.backends.dafny.preamble import PREAMBLE, PREAMBLE_NAMES
from veripy.backends.dafny import unicode_strings, regex_strings, checksum_sequences, percent_decoding
PREAMBLE_NAMES = PREAMBLE_NAMES | unicode_strings.NAMES | regex_strings.NAMES | percent_decoding.NAMES


class ProofSymbols(frozenset):
    """Lemma names with separately tracked, defined ghost predicates."""
    def __new__(cls, lemmas=(), predicates=()):
        value = super().__new__(cls, lemmas)
        value.predicates = frozenset(predicates)
        return value


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
    predicates: set[str] = set()
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
            if words[idx] == "predicate" and idx + 1 < len(words):
                predicates.add(words[idx + 1])
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
    return ProofSymbols(lemmas, predicates)


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


def _dafny_type(ann: ast.expr | None, where: ast.AST, records: dict | None = None) -> str:
    if ann is None:
        raise _err(where, "missing type annotation (the fragment requires precise types)")
    if ast.unparse(ann) == 'tuple[str, bool] | tuple[None, None]':return '(PyOpt<string>, PyOpt<bool>)'
    if ast.unparse(ann) == 'ds.ETags':return 'VHttpETags'
    match ann:
        case ast.Name(id=name) if records and name in records:
            return record_type(name)
        case ast.Name(id="int"):
            return "int"
        case ast.Name(id="bool"):
            return "bool"
        case ast.Name(id="str"):
            return "string"
        case ast.Subscript(value=ast.Name(id="list"), slice=inner):
            return f"seq<{_dafny_type(inner, where, records)}>"
        case ast.Subscript(value=ast.Name(id="Optional"), slice=inner):
            return f"PyOpt<{_dafny_type(inner, where, records)}>"
        case ast.Subscript(value=ast.Name(id=("tuple" | "Tuple")), slice=sl):
            elts = sl.elts if isinstance(sl, ast.Tuple) else [sl]
            if not (2 <= len(elts) <= 8):
                raise _err(where, (
                    "tuple types in the fragment have 2–8 elements "
                    "(a 1-tuple is just the element; longer tuples are "
                    "outside the slice encoder)"
                ))
            parts = [_dafny_type(e, where, records) for e in elts]
            return "(" + ", ".join(parts) + ")"
        case ast.BinOp(left=left, op=ast.BitOr(), right=ast.Constant(value=None)):
            return f"PyOpt<{_dafny_type(left, where, records)}>"
        case ast.BinOp(left=ast.Constant(value=None), op=ast.BitOr(), right=right):
            return f"PyOpt<{_dafny_type(right, where, records)}>"
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
    if lt in {"char", "string"} and rt in {"char", "string"}:
        return "string", "string"

    def bare_empty(n: ast.expr) -> bool:
        return isinstance(n, ast.List) and not n.elts

    if lt is None and bare_empty(left) and rt is not None and rt.startswith("seq<"):
        return rt, rt
    if rt is None and bare_empty(right) and lt is not None and lt.startswith("seq<"):
        return lt, lt
    return lt, rt


def _const_str(node: ast.expr) -> str | None:
    if isinstance(node, ast.Constant) and type(node.value) is str:
        return node.value
    return None


def _is_empty_list(node: ast.expr) -> bool:
    return isinstance(node, ast.List) and not node.elts


# str methods this encoder models, plus names it rejects with a rewrite
# rather than the generic "only append statements" message.
_STR_ADMITTED = frozenset({
    "join", "split", "find", "index", "startswith", "endswith", "replace",
    "strip", "lstrip", "rstrip", "count",
})
_STR_UNICODE_TABLE = frozenset({
    "lower", "upper", "isdigit", "isalpha", "isalnum", "isspace",
})
_STR_STILL_OUTSIDE = frozenset({
    "rsplit", "rfind", "splitlines", "format_map", "zfill", "ljust",
    "rjust", "partition", "rpartition", "removeprefix", "removesuffix",
})
_STR_SURFACE = _STR_ADMITTED | _STR_UNICODE_TABLE | _STR_STILL_OUTSIDE


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
    "str", "int", "divmod", "enumerate", "tuple", "reversed", "map",
})

# Imported math names the encoder resolves. NOT in _ENCODED_BUILTINS: that
# set rejects module-level bindings that shadow builtins (`from math import
# prod as sum`). Putting gcd there would illegally reject `from math import
# gcd`. Track an import table and resolve in `_call` instead.
_ADMITTED_MATH = frozenset({"gcd", "factorial", "isqrt", "prod"})
_MATH_TO_PREAMBLE = {"gcd": "PyGcd", "factorial": "PyFact", "isqrt": "PyIsqrt", "prod": "PyProd"}
_MATH_FLOAT = frozenset({
    "acos", "acosh", "asin", "asinh", "atan", "atan2", "atanh", "cbrt",
    "ceil", "copysign", "cos", "cosh", "degrees", "dist", "e", "erf",
    "erfc", "exp", "exp2", "expm1", "fabs", "floor", "fmod", "frexp",
    "fsum", "gamma", "hypot", "inf", "isclose", "isfinite", "isinf",
    "isnan", "ldexp", "lgamma", "log", "log10", "log1p", "log2", "modf",
    "nan", "nextafter", "pi", "pow", "radians", "remainder", "sin",
    "sinh", "sqrt", "tan", "tanh", "tau", "trunc", "ulp",
})
_IEEE_FLOAT_MSG = (
    "IEEE float is outside the fragment — use int isqrt/gcd/factorial, "
    "or keep this call behind a later `#@ extern`"
)
_MATH_REWRITE = (
    "use int isqrt/gcd/factorial, or keep this call behind a later "
    "`#@ extern`"
)


def _is_admitted_int_str(value: str) -> bool:
    """Optional ASCII minus, then a nonempty string of ASCII digits 0-9."""
    body = value[1:] if value.startswith("-") else value
    return bool(body) and all("0" <= c <= "9" for c in body)


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


@dataclass(frozen=True)
class _HelperSignature:
    node: ast.FunctionDef
    parameters: tuple[tuple[str, str], ...]
    returns: str
    outcome: bool = False


def _checked_defaults(node):
    """Only immutable literal defaults: no definition-time calls or shared data."""
    a = node.args
    if a.vararg or a.kwarg:
        raise _err(node, "varargs/defaults require a fixed signature and immutable literals")
    positional = [*a.posonlyargs, *a.args]
    pairs = list(zip(positional[len(positional)-len(a.defaults):], a.defaults))
    pairs += [(p, d) for p, d in zip(a.kwonlyargs, a.kw_defaults) if d is not None]
    defaults = {}
    for parameter, default in pairs:
        if not isinstance(default, ast.Constant) or type(default.value) not in (int, bool, str, type(None)):
            raise _err(default, "parameter defaults require immutable scalar literals")
        dtype = _dafny_type(parameter.annotation, parameter)
        want = _opt_inner(dtype) or dtype
        got = {int:"int", bool:"bool", str:"string"}.get(type(default.value))
        if (default.value is None and _opt_inner(dtype) is None) or (default.value is not None and got != want):
            raise _err(default, "parameter default type does not match its annotation")
        defaults[parameter.arg] = default
    return defaults


def _scalar_type(dtype: str | None) -> bool:
    inner = _opt_inner(dtype) or dtype
    return inner in {"int", "bool", "string"} or (_is_tuple(inner) and all(_scalar_type(t) for t in _tuple_elems(inner)))


def _helper_signatures(module: ast.Module, specs: ModuleSpecs, records: dict | None = None) -> dict[str, _HelperSignature]:
    """Close the executable call graph before emitting any methods.

    Resolution assumes this closed module's bindings remain unchanged at run
    time. No imported contracts, decorators, rebindings or recursive SCCs are
    admitted. The ordinary body encoder checks the rest of the pure fragment.
    """
    defs = {n.name: n for n in module.body if isinstance(n, ast.FunctionDef)}
    specified = {s.name: s for s in specs.functions}
    for spec in specs.functions:
        if spec.name not in defs:
            raise EncodeError(f"cannot locate function {spec.name!r}", spec.lineno)
    edges: dict[str, set[str]] = {name: set() for name in specified}
    for name in specified:
        for n in ast.walk(defs[name]):
            callee = (n.func.id if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in defs else
                      n.args[0].id if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "map"
                      and n.args and isinstance(n.args[0], ast.Name) and n.args[0].id in defs else None)
            if callee is not None:
                if callee not in specified or not (specified[callee].by_kind("ensures") or specified[callee].by_kind("ghost_ensures")):
                    raise _err(n, f"helper {callee!r} needs an explicit checked postcondition")
                if isinstance(n.func, ast.Name) and n.func.id == "map" and specified[callee].by_kind("requires"):
                    raise _err(n, "literal predicate map requires a helper without preconditions")
                edges[name].add(callee)
    if not any(edges.values()):
        return {}
    # Module initialization is deliberately restricted: executing arbitrary
    # top-level Python could replace even an apparently unassigned helper.
    for n in module.body:
        if isinstance(n, ast.FunctionDef):
            if n.name not in specified:
                raise _err(n, "all function bodies in a composed module must be explicitly specified")
            if n.decorator_list:
                raise _err(n, "decorated functions are outside checked helper composition")
        elif isinstance(n, ast.ClassDef) and records and n.name in records:
            pass  # independently validated frozen declarations
        elif isinstance(n, ast.ImportFrom) and n.level == 0 and n.module in {"typing", "math", "__future__", "dataclasses", "bisect"}:
            if any(a.name == "*" for a in n.names):
                raise _err(n, "star imports are outside checked helper composition")
        elif isinstance(n, ast.Import) and all(a.name in {"typing", "math", "sys"} for a in n.names):
            pass
        elif isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant) and isinstance(n.value.value, str):
            pass
        else:
            raise _err(n, "module initialization/rebinding is outside checked helper composition")
        if isinstance(n, (ast.Import, ast.ImportFrom)):
            if any((a.asname or a.name).split(".")[0] in defs for a in n.names):
                raise _err(n, "import shadows a helper binding")
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visiting:
            raise _err(defs[name], "recursive helper calls are outside the acyclic fragment")
        if name in visited:
            return
        visiting.add(name)
        for callee in sorted(edges[name]):
            visit(callee)
        visiting.remove(name)
        visited.add(name)

    for name in sorted(edges):
        visit(name)
    targets = set().union(*edges.values())
    signatures: dict[str, _HelperSignature] = {}
    for name in sorted(targets):
        node = defs[name]
        a = node.args
        _checked_defaults(node)
        parameters = tuple((p.arg, _dafny_type(p.annotation, p, records))
                           for p in (*a.posonlyargs, *a.args, *a.kwonlyargs))
        returns = _dafny_type(node.returns, node, records)
        if not all(_scalar_type(t) or t.startswith("seq<") or t.startswith("VRec") for _, t in parameters) or not (_scalar_type(returns) or returns.startswith("seq<")):
            raise _err(node, "checked helper returns require scalar/tuple or read-only sequence values")
        signatures[name] = _HelperSignature(node, parameters, returns)
    return signatures


def _localize_scalar_parameters(node, spec, reserved_names=frozenset()):
    """Keep entry values immutable while representing Python local rebinding."""
    parameters={a.arg:a for a in (*node.args.posonlyargs,*node.args.args,*node.args.kwonlyargs)}
    rebound={n.id for n in ast.walk(node) if isinstance(n,ast.Name) and isinstance(n.ctx,ast.Store)} & parameters.keys()
    if not rebound:return node,spec
    if any(_dafny_type(parameters[name].annotation,parameters[name]) not in {'int','bool','string','PyOpt<string>'} for name in rebound):
        raise _err(node,'parameter rebinding supports scalar parameters only')
    if any(isinstance(n,(ast.Lambda,ast.ListComp,ast.GeneratorExp,ast.SetComp,ast.DictComp,ast.AsyncFunctionDef)) or isinstance(n,ast.FunctionDef) and n is not node for n in ast.walk(node)):
        raise _err(node,'rebound scalar parameters do not support nested scopes')
    used={n.id for n in ast.walk(node) if isinstance(n,ast.Name)}|set(reserved_names)
    for clause in spec.clauses:
        if clause.desugared:used.update(n.id for n in ast.walk(ast.parse(clause.desugared,mode='eval')) if isinstance(n,ast.Name))
    names={}
    for name in sorted(rebound):
        local=name+'_local'
        while local in used:local+='_'
        names[name]=local;used.add(local)
    class Rename(ast.NodeTransformer):
        def visit_Name(self,n):return ast.copy_location(ast.Name(id=names.get(n.id,n.id),ctx=n.ctx),n)
        def visit_Call(self,n):
            if isinstance(n.func,ast.Name) and n.func.id=='old':return n
            return self.generic_visit(n)
    node,spec=copy.deepcopy(node),copy.deepcopy(spec)
    node.body=[Rename().visit(stmt) for stmt in node.body]
    initializers=[ast.copy_location(ast.Assign(targets=[ast.Name(id=local,ctx=ast.Store())],value=ast.Name(id=name,ctx=ast.Load())),node.body[0]) for name,local in names.items()]
    node.body=initializers+node.body;ast.fix_missing_locations(node)
    for clause in spec.clauses:
        if clause.kind in {'invariant','decreases','proof'} and clause.desugared:
            clause.desugared=ast.unparse(Rename().visit(ast.parse(clause.desugared,mode='eval')))
    return node,spec


class _MethodEncoder:
    def __init__(self, node: ast.FunctionDef, spec: FunctionSpec,
                 proof_lemmas: frozenset[str] = frozenset(),
                 source_lines: list[str] | None = None,
                 math_names: dict[str, str] | None = None,
                 math_aliases: frozenset[str] = frozenset(),
                 math_other: dict[str, str] | None = None,
                 reserved_names: frozenset[str] = frozenset(),
                 helpers: dict[str, _HelperSignature] | None = None,
                 records: dict | None = None, sequence_imports: dict | None = None,
                 module_values: dict | None = None, regex_models: dict | None = None, newtypes: dict | None = None, casts=frozenset(), exceptions: dict | None = None):
        self.node = node
        self.module_values = module_values or {}
        self.regex_models = regex_models or {}
        self.newtypes = newtypes or {}
        self.casts = casts
        self.exceptions = exceptions or {}
        self.spec = spec
        self.proof_lemmas = proof_lemmas
        self.proof_predicates = getattr(proof_lemmas, "predicates", frozenset())
        self.source_lines = source_lines or []
        from veripy.backends.dafny import http_lists
        try:
            self.http_list_names = http_lists.imports(ast.parse("\n".join(self.source_lines)))
            self.percent_names = percent_decoding.imports(ast.parse("\n".join(self.source_lines)))
        except ValueError as exc:raise EncodeError(str(exc), node.lineno) from exc
        self.math_names = math_names or {}
        self.math_aliases = math_aliases
        self.math_other = math_other or {}
        self.helpers = helpers or {}
        self.records = records or {}
        self.sequence_imports = sequence_imports or {}
        self.quantified_functions: dict[str, tuple[str, list[str], int]] = {}
        self._abstracting_quantifier = False
        self._quantifier_context = []
        self._compiled_requirements = []
        self._spec_clause_kind = None
        self._spec_clause_line = node.lineno
        self.record_fields = {record_type(name): {field: _dafny_type(ann, node, self.records)
                                                  for field, ann in fields}
                              for name, fields in self.records.items()}
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
        if "result" in self.params:
            raise EncodeError("parameter named 'result' shadows the postcondition result", node.lineno)
        self._shadowed = set(self.params)
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
                self._shadowed.add(name)
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
        if self.helpers:
            clashes = self._shadowed & self.helpers.keys()
            if clashes:
                raise _err(node, f"local binding shadows a helper: {sorted(clashes)!r}")
            if any(isinstance(n, (ast.Global, ast.Nonlocal, ast.FunctionDef,
                                  ast.AsyncFunctionDef, ast.ClassDef))
                   for stmt in node.body for n in ast.walk(stmt)):
                raise _err(node, "nested scopes/global/nonlocal are outside checked helper composition")
        self.scopes: list[set[str]] = [set()]
        self.retired: set[str] = set()
        self.spec_mode = False
        self.return_type: str | None = None

        self.used_names = self._collect_used_names() | set(reserved_names)
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
        taken = set(self.used_names) | set(PREAMBLE_NAMES)
        for name in sorted(self.used_names):
            if name in DAFNY_KEYWORDS or name.startswith("_") or name == "result":
                # Dafny rejects user identifiers beginning with underscore.
                # Preserve private Python names via a collision-free mapping,
                # exactly as for identifiers that are Dafny keywords.
                candidate = f"py{name}" if name.startswith("_") else f"{name}_py"
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

    def _known_nonnegative(self, node):
        if isinstance(node, ast.Constant):
            return type(node.value) is int and node.value >= 0
        if isinstance(node, ast.Name):
            return node.id in self.nonneg
        if (self.spec_mode and isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "loop_index" and not node.args and not node.keywords
                and getattr(self, "iteration_cursor", None) is not None):
            return True
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mult)):
            return self._known_nonnegative(node.left) and self._known_nonnegative(node.right)
        return False

    def _normalize_enumerated_comp(self, node):
        # The supported source is an exact list name, evaluated once by Python.
        # The fragment forbids changes to it during this pure comprehension.
        if not isinstance(node, ast.ListComp) or len(node.generators) != 1:
            return node
        c = node.generators[0]
        if not (isinstance(c.target, ast.Tuple) and len(c.target.elts) == 2
                and all(isinstance(x, ast.Name) for x in c.target.elts)
                and isinstance(c.iter, ast.Call) and isinstance(c.iter.func, ast.Name)
                and c.iter.func.id == "enumerate" and len(c.iter.args) == 1
                and isinstance(c.iter.args[0], ast.Name) and not c.iter.keywords and not c.is_async):
            return node
        index, value = [x.id for x in c.target.elts]
        if index == value or any(n in self.types or n in self.name_overrides for n in (index, value)):
            raise _err(node, "enumerated comprehension names must be distinct and unbound")
        if not (self._infer(c.iter.args[0]) or "").startswith("seq<"):
            raise _err(node, "enumerated comprehension requires a list")
        if any(isinstance(n, (ast.GeneratorExp, ast.ListComp, ast.Lambda, ast.NamedExpr))
               for e in [node.elt, *c.ifs] for n in ast.walk(e)):
            raise _err(node, "nested scopes/rebinding in enumerated comprehensions are unsupported")
        source = c.iter.args[0]
        class Replace(ast.NodeTransformer):
            def visit_Name(self, n):
                if n.id == value and isinstance(n.ctx, ast.Load):
                    return ast.copy_location(ast.Subscript(value=copy.deepcopy(source),
                        slice=ast.Name(id=index, ctx=ast.Load()), ctx=ast.Load()), n)
                return n
        result = copy.deepcopy(node)
        result.elt = Replace().visit(result.elt)
        cc = result.generators[0]
        cc.ifs = [Replace().visit(e) for e in cc.ifs]
        cc.target = ast.copy_location(ast.Name(id=index, ctx=ast.Store()), c.target)
        cc.iter = ast.copy_location(ast.Call(func=ast.Name(id="range", ctx=ast.Load()),
            args=[ast.Call(func=ast.Name(id="len", ctx=ast.Load()), args=[copy.deepcopy(source)], keywords=[])], keywords=[]), c.iter)
        return ast.fix_missing_locations(result)

    def _identity_cast(self, node):
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name) or node.func.id in self._shadowed:
            return None
        name = node.func.id
        if name in self.casts:
            if len(node.args) != 2 or node.keywords:
                raise _err(node, "cast requires a modeled NewType and one scalar value")
            target = node.args[0]
            alias = target.id if isinstance(target, ast.Name) else target.value if isinstance(target, ast.Constant) else None
            if alias not in self.newtypes or isinstance(target,ast.Name) and alias in self._shadowed:
                raise _err(node, "cast target requires an explicit NewType model")
            value = node.args[1]
        elif name in self.newtypes:
            if len(node.args) != 1 or node.keywords:raise _err(node, "NewType requires one scalar value")
            alias, value = name, node.args[0]
        else:return None
        dtype = {"str":"string", "int":"int", "bool":"bool"}[self.newtypes[alias]]
        if self._infer(value) != dtype:raise _err(node, "NewType identity model requires its exact builtin scalar type")
        return value

    def _infer(self, node: ast.expr) -> str | None:
        from veripy.backends.dafny import http_lists
        if isinstance(node, ast.Call):
            percent = percent_decoding.call_model(self, node)
            if percent is not None:return percent[0]
            http = http_lists.call_model(self, node)
            if http is not None:return http[0]
        identity = self._identity_cast(node)
        if identity is not None:return self._infer(identity)
        if isinstance(node, ast.Call):
            regex = regex_strings.call_model(self, node)
            if regex is not None:return regex[0]
        if (self.spec_mode and isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "ghost"):
            return "bool"
        node = self._normalize_enumerated_comp(node)
        match node:
            case ast.Attribute(value=ast.Name(id=name), attr="maxsize") if self.sequence_imports.get(name) == "sys" and name not in self._shadowed:
                return "int"
            case ast.Call(func=ast.Name(id=name)) if self.sequence_imports.get(name) == "bisect_right" and name not in self._shadowed:
                return "int"
            case ast.Attribute(value=value, attr=attr):
                return self.record_fields.get(self._infer(value), {}).get(attr)
            case ast.Call(func=ast.Name(id=name)) if name in self.helpers:
                return self.helpers[name].returns
            case ast.Call(func=ast.Name(id=name)) if name in self.records and name not in self._shadowed:
                return record_type(name)
            case ast.Constant(value=bool()):
                return "bool"
            case ast.Constant(value=int()):
                return "int"
            case ast.Constant(value=str()):
                return "string"
            case ast.Name(id="result") if self.spec_mode and self._spec_clause_kind in {"ensures", "ghost_ensures"}:
                return self.return_type
            case ast.Name(id=name):
                if name not in self._shadowed and name not in self.types and name not in self.name_overrides and name in self.module_values:
                    from veripy.backends.dafny.environment import literal
                    return self._infer(literal(self.module_values[name], node))
                return self.types.get(name)
            case ast.UnaryOp(op=ast.Not()):
                return "bool"
            case ast.UnaryOp(op=ast.USub(), operand=operand):
                return "int" if self._infer(operand) == "int" else None
            case ast.BoolOp() | ast.Compare():
                return "bool"
            case ast.BinOp(left=left, op=op, right=right):
                if self._literal_repeat(node):
                    return self._infer(left)
                lt, rt = self._infer(left), self._infer(right)
                if isinstance(op, (ast.FloorDiv, ast.Mod)):
                    return "int" if lt == "int" and rt == "int" else None
                if isinstance(op, ast.Add) and {lt,rt} == {"int","bool"}:return "int"
                if isinstance(op, ast.Add):
                    lt, rt = _concat_types(left, right, lt, rt)
                if isinstance(op, ast.Add) and lt == rt and lt is not None \
                        and (lt == "string" or lt.startswith("seq<")):
                    return lt  # concatenation: same meaning in both languages
                if lt == "int" and rt == "int":
                    return "int"
                return None
            case ast.Call(func=ast.Name(id="tuple"), args=[ast.GeneratorExp() as gen], keywords=[]):
                dtype = self._infer(ast.copy_location(ast.ListComp(elt=gen.elt, generators=gen.generators), gen))
                return f"VChecksumTuple<{dtype[4:-1]}>" if dtype and dtype.startswith("seq<") else None
            case ast.Call(func=ast.Name(id="len")):
                return "int"
            case ast.Call(func=ast.Name(id="loop_index")) if self.spec_mode:
                return "int"
            case ast.Call(func=ast.Name(id="divmod"), args=[left, right], keywords=[]):
                return "(int, int)" if self._eff_type(left) == self._eff_type(right) == "int" else None
            case ast.Call(func=ast.Name(id="str"), args=[arg], keywords=[]):
                return "string" if self._infer(arg) in {"int", "string"} else None
            case ast.Call(func=ast.Name(id="int"), args=[arg], keywords=[]):
                return "int" if self._infer(arg) == "string" else None
            case ast.Call(func=ast.Name(id=("min" | "max" | "abs" | "sum"))):
                return "int"
            case ast.Call(func=ast.Name(id="bool")):
                return "bool"
            case ast.Call(func=ast.Name(id="sorted"), args=[arg], keywords=[]):
                dtype = self._infer(arg)
                return dtype if dtype in {"seq<int>", "seq<(int, int)>", "seq<(int, int, int)>"} else None
            case ast.Call(func=ast.Name(id="sorted")):
                return "seq<int>"  # the separately checked keyed range form
            case ast.Call(func=ast.Name(id=("all" | "any"))):
                return "bool"
            case ast.Call(func=ast.Name(id="old"), args=[ast.Name(id=name)]):
                return self.types.get(name)
            case ast.Call() as call if self._admitted_math_canon(call) is not None:
                return "int"
            case ast.Subscript(value=value, slice=ast.Slice()):
                return self._eff_type(value)  # slicing projects Optional with a VC
            case ast.Subscript(value=value, slice=index):
                base = self._infer(value)
                if _is_tuple(_opt_inner(base)):
                    base = _opt_inner(base)
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
                if checksum_sequences.element(base):
                    return checksum_sequences.element(base)
                if base == "string":
                    return "char"
                if base is not None and base.startswith("seq<"):
                    return base[4:-1]
                return None
            case ast.IfExp(test=test, body=body, orelse=orelse):
                bt, ot = self._infer(body), self._infer(orelse)
                if bt == ot:
                    return bt
                if (isinstance(test, ast.Compare) and isinstance(test.left, ast.Name)
                        and len(test.ops) == len(test.comparators) == 1
                        and isinstance(test.comparators[0], ast.Constant)
                        and test.comparators[0].value is None):
                    selected = body if isinstance(test.ops[0], ast.IsNot) else orelse if isinstance(test.ops[0], ast.Is) else None
                    if isinstance(selected, ast.Name) and selected.id == test.left.id:
                        inner = _opt_inner(self._infer(selected))
                        other = ot if selected is body else bt
                        if inner is not None and inner == other:
                            return inner
                return None
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
            case ast.Call(func=ast.Attribute() as attr):
                return self._infer_str_method(attr.attr, attr.value)
            case _:
                return None

    def _infer_str_method(self, method: str, receiver: ast.expr) -> str | None:
        """Result types for admitted str methods. Infer only when the
        receiver is a str so a rejected `.lower()` does not type as
        string and then fail later on a different rule."""
        if self._infer(receiver) != "string":
            return None
        if method in ("join", "replace", "strip", "lstrip", "rstrip", "lower"):
            return "string"
        if method == "split":
            return "seq<string>"
        if method in ("find", "count", "index"):
            return "int"
        if method in ("startswith", "endswith"):
            return "bool"
        return None

    def _comp_binder_type(self, comp: ast.comprehension) -> str | None:
        it = comp.iter
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) \
                and it.func.id == "range" and 1 <= len(it.args) <= 2 \
                and not it.keywords:
            return "int"
        if (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "reversed"
                and len(it.args) == 1 and not it.keywords):
            dtype = self._infer(it.args[0])
            return "char" if dtype == "string" else dtype[4:-1] if dtype and dtype.startswith("seq<") else checksum_sequences.element(dtype)
        dt = self._infer(it)
        if dt == "string":return "char"
        if checksum_sequences.element(dt):return checksum_sequences.element(dt)
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

    def _literal_repeat(self, node: ast.expr) -> bool:
        return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult)
                and isinstance(node.left, ast.List) and len(node.left.elts) == 1
                and isinstance(node.left.elts[0], ast.Constant)
                and type(node.left.elts[0].value) in {int, bool, str}
                and self._infer(node.right) == "int")

    def expr(self, node: ast.expr) -> str:
        if (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.attr == "maxsize"
                and self.sequence_imports.get(node.value.id) == "sys" and node.value.id not in self._shadowed):
            import sys
            return str(sys.maxsize)
        node = self._normalize_enumerated_comp(node)
        match node:
            case ast.Constant(value=bool() as b):
                return "true" if b else "false"
            case ast.Constant(value=int() as i):
                return str(i)
            case ast.Constant(value=str() as s):
                return self._escape_str(s, node)
            case ast.Name(id=name):
                # The return-value intrinsic has precedence over module constants.
                if name == "result" and self.spec_mode and self._spec_clause_kind in {"ensures", "ghost_ensures"}:
                    return "result"
                if name not in self._shadowed and name not in self.types and name not in self.name_overrides and name in self.module_values:
                    from veripy.backends.dafny.environment import literal
                    return self.expr(literal(self.module_values[name], node))
                if name in self.name_overrides:
                    return self.name_overrides[name]
                if name == "result":
                    if name not in self.types:
                        raise _err(node, "`result` requires a local binding outside postconditions")
                if name in self.retired:
                    raise _err(node, (
                        f"loop index {name!r} used after its loop — Python leaves it at "
                        f"the last iterated value (or unbound), the lowering does not; "
                        f"outside the slice-1 encoder"
                    ))
                if name not in self._shadowed:
                    if name in self.math_other:
                        orig = self.math_other[name]
                        raise _err(node, (
                            _IEEE_FLOAT_MSG if orig in _MATH_FLOAT
                            else f"math.{orig} is outside the fragment — {_MATH_REWRITE}"
                        ))
                    if name in self.math_names:
                        raise _err(node, (
                            f"{name} is a math function — call it as "
                            f"{name}(...), or {_MATH_REWRITE}"
                        ))
                return self._mangle(name)
            case ast.UnaryOp(op=ast.Not(), operand=operand):
                if self._is_seqish(self._infer(operand)):
                    # §7.3 truthiness: `not xs` on a list/str means emptiness.
                    return f"(|{self.expr(operand)}| == 0)"
                if _is_tuple(self._infer(operand)):
                    # All admitted tuples have fixed, nonzero arity. Retain
                    # evaluation (and bounds/call VCs) of the operand.
                    return f"(var {self._fresh('tuple_truth')} := {self.expr(operand)}; false)"
                return f"!({self._bool_ctx(operand)})"
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
                if self._literal_repeat(node):
                    n = self.expr(right)
                    return f"seq((if {n} > 0 then {n} else 0), {self._fresh('repeat_index')} => {self.expr(left.elts[0])})"
                if isinstance(op, ast.RShift):
                    shift = _const_int_index(right)
                    if self._infer(left) != "int" or shift is None or not 0 <= shift <= 4096:
                        raise _err(node,"right shift requires an integer and a bounded nonnegative literal shift")
                    return f"PyFloorDiv({self.expr(left)}, {1 << shift})"
                if isinstance(op, ast.BitAnd):
                    mask = _const_int_index(right); value = left
                    if mask is None:mask = _const_int_index(left); value = right
                    if mask is None or mask < 0 or (mask & (mask + 1)) != 0 or self._infer(value) != "int":
                        raise _err(node,"bitwise and requires an integer and a literal low-bit mask")
                    return f"PyMod({self.expr(value)}, {mask+1})"
                if type(op) not in self._ARITH_SYMBOL:
                    raise _err(node, f"operator {type(op).__name__} is outside the slice-1 encoder")
                # Operand types BEFORE emission: everything below assumes
                # them, and Dafny's own complaint arrives too late and in
                # the wrong vocabulary.
                self._check_arith(node, op, left, right)
                l, r = self._deopt(left), self._deopt(right)
                match op:
                    case ast.Add():
                        if self._eff_type(left) == "bool":l = f"(if {l} then 1 else 0)"
                        if self._eff_type(right) == "bool":r = f"(if {r} then 1 else 0)"
                        if self._eff_type(left) == "char":
                            l = f"[{l}]"
                        if self._eff_type(right) == "char":
                            r = f"[{r}]"
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
                result_type = self._infer(node)
                def branch(value):
                    return self._deopt(value) if result_type is not None and _opt_inner(self._infer(value)) == result_type else self.expr(value)
                return f"(if {self.expr(test)} then {branch(body)} else {branch(orelse)})"
            case ast.Subscript(value=value, slice=index):
                if isinstance(index, ast.Slice):
                    dtype = self._infer(value)
                    if _is_tuple(dtype):raise _err(node, "slicing a fixed tuple is outside the slice encoder")
                    base = self._deopt(value)
                    immutable = checksum_sequences.element(dtype) is not None
                    if immutable:base = f"({base}).VChecksumValues"
                    lo = self.expr(index.lower) if index.lower is not None else "0"
                    hi = self.expr(index.upper) if index.upper is not None else f"|{base}|"
                    if index.step is not None:
                        step = _const_int_index(index.step)
                        if step is None or step <= 0:raise _err(node, "slice steps require a positive literal integer")
                        result = f"VChecksumStride({base}, {lo}, {hi}, {step})"
                    else:result = f"PySlice({base}, {lo}, {hi})"
                    return f"VChecksumTupleMake({result})" if immutable else result
                if checksum_sequences.element(self._infer(value)):
                    base = f"({self.expr(value)}).VChecksumValues"
                    return f"{base}[PyIndex({self.expr(index)}, |{base}|)]"
                if _is_tuple(self._infer(value)) or _is_tuple(_opt_inner(self._infer(value))):
                    return self._tuple_index_expr(node, value, index)
                base = self.expr(value)
                idx = self.expr(index)
                # Python normalizes negative indices from the end; Dafny does
                # not. PyIndex carries Python's exact semantics (its requires
                # is exactly Python's IndexError condition). Indices provably
                # >= 0 — nonneg literals and tracked 0-based binders/loop
                # variables — are emitted BARE so spec quantifier triggers
                # match the body's ground terms; everything else is wrapped.
                provably_nonneg = self._known_nonnegative(index)
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
            case ast.Attribute(value=ast.Name(id=base), attr=attr) \
                    if base in self.math_aliases and base not in self._shadowed:
                raise _err(node, (
                    _IEEE_FLOAT_MSG if attr in _MATH_FLOAT
                    else f"math.{attr} is outside the fragment — {_MATH_REWRITE}"
                ))
            case ast.Attribute(value=value, attr=attr) if self._infer(value) in self.record_fields:
                if attr not in self.record_fields[self._infer(value)]:
                    raise _err(node, f"unknown record field {attr!r}")
                return f"({self.expr(value)}).{record_field(attr)}"
            case _:
                raise _err(node, f"expression {type(node).__name__} is outside the slice-1 encoder "
                                 f"-- see the admitted-construct table in docs/SEMANTICS.md")

    def _tuple_index_expr(self, node: ast.Subscript, value: ast.expr,
                          index: ast.expr) -> str:
        """Project `p[k]` as Dafny `p.k`. The index is a constant (negative
        wrap is Python's); a variable index would treat a product as a
        sequence, which Dafny tuples are not."""
        elems = _tuple_elems(_opt_inner(self._infer(value)) or self._infer(value) or "")
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
        base = self._deopt(value)
        if not isinstance(value, ast.Name) or _opt_inner(self._infer(value)) is not None:
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
            reverse = (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "reversed"
                       and len(it.args) == 1 and not it.keywords)
            source = it.args[0] if reverse else it
            dt = self._infer(source)
            if not (dt == "string" or checksum_sequences.element(dt) or dt and dt.startswith("seq<")):
                raise _err(node, "comprehension sources must be range(...) or a finite sequence")
            src = self.expr(source)
            if checksum_sequences.element(dt):src = f"({src}).VChecksumValues"
            if reverse:src = f"VChecksumReverse({src})"
            count = f"|{src}|"
            override = f"{src}[{idx}]"
            binder_type = "char" if dt == "string" else checksum_sequences.element(dt) or dt[4:-1]
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
                "— write `str(n)` and concatenate, or write the digits "
                "as a literal"
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
        if isinstance(op, ast.Add) and {lt,rt} == {"int","bool"}:return
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
            if isinstance(op,(ast.Eq,ast.NotEq,ast.In,ast.NotIn)):
                kinds=(self._infer(current) or '',self._infer(comp) or '')
                if any(token in kind for kind in kinds for token in ('VRegexMatch','VHttpMatch','VHttpETags','VCharsetCapture')):
                    raise _err(node,'modeled dependency objects support presence checks, not value equality or containment, including inside containers')
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
                if {"PyOpt<VRegexMatch>","PyOpt<VHttpMatch>","PyOpt<VCharsetCapture>"} & {lt,rt}:raise _err(node,"regex match objects support presence checks, not value equality")
                if (checksum_sequences.element(lt) or checksum_sequences.element(rt)) and lt != rt:
                    raise _err(node,"immutable tuple equality requires matching tuple types")
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
                if {lt, rt} == {"char", "string"}:
                    # Python indexing returns a length-one str. Lift the model
                    # character before comparing with strings of any length.
                    l, r = self._coerce(current, "string"), self._coerce(comp, "string")
                else:
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
                    rt = self._eff_type(comp)
                    if rt == "string" and self._infer(current) in {"string", "char"}:
                        needle = self._coerce(current, "string")
                        parts.append(f"(PyStrFind({self._deopt(comp)}, {needle}) {'>=' if isinstance(op, ast.In) else '<'} 0)")
                        current = comp
                        continue
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

    def _math_live(self, name: str) -> bool:
        """True when `name` still denotes a module-level math import here."""
        return name not in self._shadowed

    def _admitted_math_canon(self, node: ast.Call) -> str | None:
        """`gcd`/`factorial`/`isqrt` when this call is an imported math site."""
        func = node.func
        if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
            base = func.value.id
            if (base in self.math_aliases and self._math_live(base)
                    and func.attr in _ADMITTED_MATH):
                return func.attr
            return None
        if isinstance(func, ast.Name) and self._math_live(func.id):
            return self.math_names.get(func.id)
        return None

    def _reject_other_math(self, node: ast.Call) -> None:
        """IEEE-float / rest-of-math diagnostic when the call is a math site."""
        func = node.func
        attr: str | None = None
        if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
            base = func.value.id
            if base in self.math_aliases and self._math_live(base):
                attr = func.attr
        elif isinstance(func, ast.Name) and self._math_live(func.id):
            attr = self.math_other.get(func.id)
        if attr is None:
            return
        raise _err(node, (
            _IEEE_FLOAT_MSG if attr in _MATH_FLOAT
            else f"math.{attr} is outside the fragment — {_MATH_REWRITE}"
        ))

    def _emit_math(self, canon: str, node: ast.Call) -> str:
        py = _MATH_TO_PREAMBLE[canon]
        if node.keywords:
            raise _err(node, (
                f"keyword arguments to math.{canon}() are outside the fragment "
                f"— {_MATH_REWRITE}"
            ))
        args = node.args
        if canon == "prod":
            if len(args) != 1 or self._infer(args[0]) != "seq<int>":
                raise _err(node, "math.prod requires one list[int], without start")
            return f"PyProd({self.expr(args[0])})"
        if canon == "gcd":
            if len(args) != 2:
                raise _err(node, (
                    "math.gcd is admitted for exactly two ints "
                    "(Python 3.9+ gcd is *args) — pass two integers, or "
                    "keep this call behind a later `#@ extern`"
                ))
            for a in args:
                if self._eff_type(a) != "int":
                    raise _err(node, "math.gcd needs int operands")
            return f"{py}({self._deopt(args[0])}, {self._deopt(args[1])})"
        if len(args) != 1:
            raise _err(node, (
                f"math.{canon} is admitted for one non-negative int — "
                f"drop extra arguments, or keep this call behind a later "
                "`#@ extern`"
            ))
        if self._eff_type(args[0]) != "int":
            raise _err(node, f"math.{canon} needs an int operand")
        return f"{py}({self._deopt(args[0])})"

    def _call(self, node: ast.Call) -> str:
        from veripy.backends.dafny import http_lists
        percent = percent_decoding.call_model(self, node)
        if percent is not None:return percent[1]
        http = http_lists.call_model(self, node)
        if http is not None:return http[1]
        identity = self._identity_cast(node)
        if identity is not None:return self.expr(identity)
        regex = regex_strings.call_model(self, node)
        if regex is not None:return regex[1]
        if isinstance(node.func, ast.Name) and node.func.id in self.records:
            name = node.func.id
            fields = self.records[name]
            if name in self._shadowed or self._has_helper(node):
                raise _err(node, "record constructors require an unshadowed schema and pure scalar arguments")
            if any(not isinstance(ann, ast.Name) or ann.id not in {"int", "bool", "str"} for _, ann in fields):
                raise _err(node, "record construction currently supports scalar fields only")
            if len(node.args) > len(fields) or any(isinstance(a, ast.Starred) for a in node.args):
                raise _err(node, "record constructor has too many or unpacked arguments")
            values = list(zip((field for field, _ in fields), node.args))
            for kw in node.keywords:
                if kw.arg is None or kw.arg not in dict(fields) or kw.arg in dict(values):
                    raise _err(node, "record constructor has unpacked, unknown or duplicate keywords")
                values.append((kw.arg, kw.value))
            if len(values) != len(fields):
                raise _err(node, "record constructor requires every field")
            temps = {}
            bindings = []
            for field, value in values:
                want = _dafny_type(dict(fields)[field], node, self.records)
                if self._infer(value) != want:
                    raise _err(value, "record constructor argument must match its scalar field type")
                temp = self._fresh("record_arg")
                temps[field] = temp
                bindings.append(f"var {temp} := {self.expr(value)}; ")
            # Let bindings retain Python's positional/keyword evaluation order.
            result = record_constructor(name) + "(" + ", ".join(temps[field] for field, _ in fields) + ")"
            return "(" + "".join(bindings) + result + ")"
        if isinstance(node.func, ast.Name) and node.func.id == "ghost":
            if (not self.spec_mode or self._spec_clause_kind not in {"invariant", "proof", "ghost_ensures"}
                    or node.keywords or not node.args or not isinstance(node.args[0], ast.Constant)
                    or type(node.args[0].value) is not str or node.args[0].value not in self.proof_predicates):
                raise _err(node, "ghost() requires a defined sidecar predicate name in an invariant or proof argument")
            return node.args[0].value + "(" + ", ".join(self.expr(a) for a in node.args[1:]) + ")"
        if (isinstance(node.func, ast.Name) and self.sequence_imports.get(node.func.id) == "bisect_right"
                and node.func.id not in self._shadowed):
            if node.keywords or len(node.args) != 2 or self._infer(node.args[0]) != "seq<(int, int)>" or self._infer(node.args[1]) != "(int, int)":
                raise _err(node, "bisect_right supports an integer-pair list and integer-pair key only")
            seq, key = map(self.expr, node.args)
            return f"PyBisect2({seq}, {key}, 0, |{seq}|)"
        if isinstance(node.func, ast.Name) and node.func.id in self.helpers:
            context = "spec expressions" if self.spec_mode else "this expression context"
            raise _err(node, f"executable helper calls are outside {context}")
        math = self._admitted_math_canon(node)
        if math is not None:
            return self._emit_math(math, node)
        self._reject_other_math(node)
        func = node.func
        if isinstance(func, ast.Attribute):
            return self._str_method(node, func)
        if not isinstance(func, ast.Name):
            raise _err(node, "method calls are outside the slice-1 encoder -- only "
                             "`xs.append(v)` statements are modeled")
        name = func.id
        args = node.args
        if name == "loop_index":
            cursor = getattr(self, "iteration_cursor", None)
            if not self.spec_mode or cursor is None or args or node.keywords:
                raise _err(node, "loop_index() requires a for-each loop annotation and no arguments")
            return cursor
        if name == "sorted":
            # Reuse the checked lexicographic models used by list.sort.
            model = {"seq<int>": "PySorted", "seq<(int, int)>": "PySorted2",
                     "seq<(int, int, int)>": "PySorted3"}.get(
                         self._infer(args[0]) if len(args) == 1 else None)
            if node.keywords or model is None:
                raise _err(node, (
                    "sorted() takes a list[int] or a list of integer pairs/triples — "
                    "drop key=/reverse=; other element types remain outside the fragment"
                ))
            return f"{model}({self.expr(args[0])})"
        if node.keywords:
            # No encoded builtin takes keywords; silently dropping one
            # (e.g. max(a, b, key=abs)) would change the meaning.
            raise _err(node, f"keyword arguments to {name}() are outside the fragment")
        if name == "divmod":
            if len(args) != 2 or any(self._eff_type(a) != "int" for a in args):
                raise _err(node, "divmod() requires exactly two int operands in the fragment")
            # Expressions are pure; use the already modeled Python floor /
            # remainder semantics, including negative divisors. Both helpers
            # require b != 0, so a possible ZeroDivisionError remains a VC.
            left, right = self._deopt(args[0]), self._deopt(args[1])
            return f"(PyFloorDiv({left}, {right}), PyMod({left}, {right}))"
        if name == "bool" and len(args) == 1:return self._bool_ctx(args[0])
        if name == "tuple" and len(args) == 1 and isinstance(args[0], ast.GeneratorExp):
            gen = args[0]
            if len(gen.generators) != 1 or gen.generators[0].is_async or not isinstance(gen.generators[0].target, ast.Name):
                raise _err(node, "tuple materialization requires one synchronous generator")
            return f"VChecksumTupleMake({self._list_comp(gen, gen.elt, gen.generators[0])})"
        if name == "len" and len(args) == 1:
            t = self._infer(args[0])
            if checksum_sequences.element(t):return f"|({self.expr(args[0])}).VChecksumValues|"
            if _is_tuple(t):
                # Dafny `|p|` is sequence length; a tuple's len is its
                # (static) arity. Fragment expressions are pure, so
                # emitting the constant does not drop observable effects.
                return str(len(_tuple_elems(t)))
            return f"|{self._deopt(args[0])}|"
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
            dtype = self._infer(arg)
            if checksum_sequences.element(dtype) == "int":return f"PySum(({self.expr(arg)}).VChecksumValues)"
            if _is_tuple(dtype) and all(t == "int" for t in _tuple_elems(dtype)):
                value = self.expr(arg)
                return "(" + " + ".join(f"({value}).{i}" for i in range(len(_tuple_elems(dtype)))) + ")"
            if dtype != "seq<int>":
                raise _err(node, "sum() needs a list[int] operand in the slice encoder")
            return f"PySum({self.expr(arg)})"
        if name == "old" and self.spec_mode and len(args) == 1 and isinstance(args[0], ast.Name):
            # Parameters are immutable in the fragment (ownership + copy-in).
            if args[0].id not in self.params:
                raise _err(node, "old() takes a parameter name")
            return self._mangle(args[0].id)
        if name == "bool" and self.spec_mode and len(args) == 1:
            if self._infer(args[0]) == "int":
                return f"({self.expr(args[0])} != 0)"
            if self._infer(args[0]) != "bool":
                raise _err(node, (
                    "truthiness in specs is outside the fragment — write an explicit "
                    "comparison (e.g. `x != 0`) instead of relying on bool(<non-bool>)"
                ))
            return f"({self.expr(args[0])})"
        if name in ("all", "any") and len(args) == 1 and isinstance(args[0], ast.Call):
            from veripy.frontend.literal_map import expand_literal_map
            try: expanded = expand_literal_map(node, {k:v.node for k,v in self.helpers.items()})
            except ValueError as exc: raise _err(node, str(exc)) from exc
            if expanded is not None:
                if self._infer(args[0].args[1]) != "string":raise _err(node, "literal predicate map requires a string iterable")
                return self._quantifier(name, expanded.args[0])
        if name in ("all", "any") and len(args) == 1 \
                and isinstance(args[0], ast.GeneratorExp):
            return self._quantifier(name, args[0])
        if name == "str":
            if len(args) != 1:
                raise _err(node, (
                    "str() in this slice takes one int — not zero args, "
                    "not a sequence; this slice admits str(int) only"
                ))
            t = self._infer(args[0])
            if t == "string":return self.expr(args[0])
            if t == "int":
                return f"PyIntToStr({self.expr(args[0])})"
            if t == "bool":
                raise _err(node, (
                    "str() of bool is outside this slice — bool is a "
                    "disjoint sort — write `'True'`/`'False'` literals "
                    "or compare explicitly"
                ))
            raise _err(node, (
                f"str() of {_py_type_name(t)} is outside this slice — "
                "this slice admits str(int) only"
            ))
        if name == "int":
            if len(args) != 1:
                raise _err(node, (
                    "int() in this slice parses a digit string — one "
                    "positional str, no base, no keywords"
                ))
            t = self._infer(args[0])
            if t == "string":
                arg = args[0]
                if isinstance(arg, ast.Constant) and isinstance(arg.value, str) \
                        and not _is_admitted_int_str(arg.value):
                    raise _err(node, (
                        "int() of a non-digit string is outside this "
                        "slice — strip whitespace / drop `_`/`+`"
                    ))
                return f"PyStrToInt({self.expr(arg)})"
            if t == "int":
                raise _err(node, (
                    "int() of an int is outside this slice — int() in "
                    "this slice parses a digit string"
                ))
            raise _err(node, (
                f"int() of {_py_type_name(t)} is outside this slice — "
                "int() in this slice parses a digit string"
            ))
        raise _err(node, f"call to {name!r} is outside the slice-1 encoder")

    def _require_str_arg(self, node: ast.Call, method: str, arg: ast.expr,
                         what: str) -> str:
        t = self._infer(arg)
        if t == "char":return f"[{self.expr(arg)}]"
        if t != "string":
            raise _err(node, (
                f".{method}() is outside the fragment because {what} is "
                f"{_py_type_name(t)}, not str — pass a str"
            ))
        return self.expr(arg)

    def _str_method(self, node: ast.Call, func: ast.Attribute) -> str:
        method = func.attr
        if method not in _STR_SURFACE:
            raise _err(node, (
                "method calls are outside the slice-1 encoder -- only "
                "`xs.append(v)` statements are modeled"
            ))
        if node.keywords:
            raise _err(node, (
                f"keyword arguments to .{method}() are outside the fragment "
                "because they would be silently dropped — pass positional "
                "arguments"
            ))
        recv_t = self._eff_type(func.value)
        if recv_t != "string":
            raise _err(node, (
                f".{method}() is outside the fragment because the receiver "
                f"is {_py_type_name(recv_t)}, not str — call it on a str "
                "(or annotate the receiver)"
            ))
        recv = self._deopt(func.value)
        args = node.args
        if method == "index":
            if len(args) != 1 or self._infer(args[0]) not in {"string", "char"}:
                raise _err(node, ".index() requires one string needle")
            return f"VChecksumIndex({recv}, {self._coerce(args[0], 'string')})"
        if method == "lower":
            if args:raise _err(node, ".lower() takes no arguments")
            return f"VUnicodeLower({recv})"
        if method in _STR_UNICODE_TABLE:
            raise _err(node, (
                f".{method}() is outside the fragment because Unicode-table "
                "methods would be a silent ASCII approximation — this slice "
                "has no Unicode case/category tables; rewrite with an "
                "explicit ASCII check or keep the original string"
            ))
        if method in _STR_STILL_OUTSIDE:
            if method == "rsplit":
                raise _err(node, (
                    ".rsplit() is outside the fragment because this slice "
                    "models only left-to-right unlimited split — use "
                    "s.split(sep) with a nonempty sep"
                ))
            raise _err(node, (
                f".{method}() is outside the fragment because it has no "
                "model in this slice — rewrite using join/split/find/"
                "startswith/endswith/replace/strip(chars)"
            ))
        if method == "join":
            if len(args) != 1:
                raise _err(node, (
                    ".join() is outside the fragment because it takes one "
                    "list[str] of parts — pass the sequence as a single "
                    "positional argument"
                ))
            pt = self._infer(args[0])
            if pt is None and _is_empty_list(args[0]):
                pt = "seq<string>"
            if pt != "seq<string>":
                raise _err(node, (
                    ".join() is outside the fragment because the parts "
                    f"are {_py_type_name(pt)}, not list[str] — pass a "
                    "list of strings"
                ))
            return f"PyStrJoin({recv}, {self.expr(args[0])})"
        if method == "split":
            if len(args) == 0:
                raise _err(node, (
                    ".split() is outside the fragment because no-arg split "
                    "uses the Unicode whitespace table — pass an explicit "
                    "sep (e.g. s.split(' '))"
                ))
            if len(args) != 1:
                raise _err(node, (
                    ".split() is outside the fragment because maxsplit is "
                    "not in this slice — omit maxsplit for an unlimited "
                    "split"
                ))
            if _const_str(args[0]) == "":
                raise _err(node, (
                    ".split() is outside the fragment because an empty sep "
                    "raises ValueError in Python — pass a nonempty sep"
                ))
            sep = self._require_str_arg(node, method, args[0], "sep")
            return f"PyStrSplit({recv}, {sep})"
        if method == "count":
            if len(args) != 1:
                raise _err(node, "str.count supports one substring; start/end are outside the fragment")
            sub = self._require_str_arg(node, method, args[0], "the substring")
            return f"PyStrCount({recv}, {sub})"
        if method == "find":
            if len(args) != 1:
                raise _err(node, (
                    ".find() is outside the fragment because it takes one "
                    "substring in this slice — drop start/end or slice the "
                    "receiver first"
                ))
            sub = self._require_str_arg(node, method, args[0], "the substring")
            return f"PyStrFind({recv}, {sub})"
        if method in ("startswith", "endswith"):
            kind = "prefix" if method == "startswith" else "suffix"
            fn = "PyStrStartsWith" if method == "startswith" else "PyStrEndsWith"
            if not 1 <= len(args) <= 3:
                raise _err(node, f".{method}() requires a {kind} and at most two integer bounds")
            bounds = ""
            if len(args) > 1:
                if any(self._infer(bound) != "int" for bound in args[1:]):
                    raise _err(node, f".{method}() start/end bounds require exact integers")
                start = self.expr(args[1])
                end = self.expr(args[2]) if len(args) == 3 else f"|{recv}|"
                bounds = f", {start}, {end}"
                fn += "Range"
            if isinstance(args[0], ast.Tuple):
                if any(not isinstance(arg, ast.Constant) or type(arg.value) is not str for arg in args[0].elts):
                    raise _err(node, "tuple prefix/suffix arguments must be literal strings")
                parts = [f"{fn}({recv}, {self._require_str_arg(node, method, arg, kind)}{bounds})" for arg in args[0].elts]
                # Even an empty tuple evaluates its bounds before matching.
                return "(" + " || ".join(parts) + ")" if parts else (f'({fn}({recv}, ""{bounds}) && false)' if bounds else "false")
            arg = self._require_str_arg(node, method, args[0], f"the {kind}")
            return f"{fn}({recv}, {arg}{bounds})"
        if method == "replace":
            if len(args) == 3:
                raise _err(node, (
                    ".replace() is outside the fragment because count is "
                    "not in this slice — omit count to replace all "
                    "occurrences"
                ))
            if len(args) != 2:
                raise _err(node, (
                    ".replace() is outside the fragment because it takes "
                    "old and new strings — pass two str arguments"
                ))
            if _const_str(args[0]) == "":
                raise _err(node, (
                    ".replace() is outside the fragment because an empty "
                    "old inserts between every character — pass a nonempty "
                    "old"
                ))
            old = self._require_str_arg(node, method, args[0], "old")
            new = self._require_str_arg(node, method, args[1], "new")
            return f"PyStrReplace({recv}, {old}, {new})"
        # strip / lstrip / rstrip
        if len(args) == 0:
            fn = {"strip":"VUnicodeStrip", "lstrip":"VUnicodeLStrip", "rstrip":"VUnicodeRStrip"}[method]
            return f"{fn}({recv})"
        if len(args) != 1:
            raise _err(node, (
                f".{method}() is outside the fragment because it takes "
                "one chars string — pass a single str"
            ))
        chars = self._require_str_arg(node, method, args[0], "chars")
        fn = {"strip": "PyStrStrip", "lstrip": "PyStrLStrip",
              "rstrip": "PyStrRStrip"}[method]
        return f"{fn}({recv}, {chars})"

    def _quantifier(self, kind: str, gen: ast.GeneratorExp) -> str:
        binders: list[str] = []
        domains: list[str] = []
        binder_names: list[str] = []
        saved_types: dict[str, str | None] = {}
        pushed_context = False
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
                    if len(domain.args) == 1 or self._known_nonnegative(domain.args[0]):
                        self.nonneg.add(raw)
                else:
                    dt = self._infer(domain)
                    if not (dt == "string" or dt is not None and dt.startswith("seq<")):
                        raise _err(gen, "quantifier domains must be range(...) or a finite sequence")
                    domains.append(f"{var} in {self.expr(domain)}")
                    binder_type = "char" if dt == "string" else dt[4:-1]
                binders.append(var)
                binder_names.append(raw)
                saved_types[raw] = self.types.get(raw)
                self.types[raw] = binder_type
                for pred in comp.ifs:
                    domains.append(self._bool_ctx(pred))
            self._quantifier_context.append((tuple(binder_names), tuple(domains)))
            pushed_context = True
            body = self.expr(gen.elt)
            if not self.spec_mode and self._eff_type(gen.elt) != "bool":
                raise _err(gen, (
                    f"{kind}() needs a bool-valued generator expression — "
                    "write an explicit comparison (e.g. `x > 0`)"
                ))
        finally:
            if pushed_context:
                self._quantifier_context.pop()
            for raw in binder_names:
                prev = saved_types.get(raw)
                if prev is None:
                    self.types.pop(raw, None)
                else:
                    self.types[raw] = prev
                self.nonneg.discard(raw)
        quant = "forall" if kind == "all" else "exists"
        connective = "==>" if kind == "all" else "&&"
        expression = f"({quant} {', '.join(binders)} :: ({' && '.join(domains)}) {connective} ({body}))"
        return self._name_input_quantifier(kind, gen, expression)

    def _name_input_quantifier(self, kind, gen, expression):
        """Share nested input-only propositions in the sweep fragment.

        These are defined ghost predicates, verified under the original input
        contracts. They avoid repeatedly skolemizing equivalent nested
        quantifiers at a postcondition and a ghost-call argument. Local state,
        results, old(), and executable expressions are never abstracted.
        """
        if (not self.spec_mode or "bisect_right" not in self.sequence_imports
                or self._abstracting_quantifier or self._spec_clause_kind == "requires"):
            return expression
        nodes = list(ast.walk(gen))
        if sum(isinstance(n, ast.GeneratorExp) for n in nodes) < 2 and not self._quantifier_context:
            return expression
        if any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
               and n.func.id in {"old", "loop_index"} for n in nodes):
            return expression
        bound = {n.target.id for n in nodes if isinstance(n, ast.comprehension)
                 and isinstance(n.target, ast.Name)}
        used = {n.id for n in nodes if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
        # Only builtins that introduce no ambient state are ignored here.
        free = used - bound - {"all", "any", "range", "len", "min", "max", "sum", "abs", "bool"}
        enclosing = {n for names, _ in self._quantifier_context for n in names}
        if not free <= self.params | enclosing:
            return expression
        captured = sorted(self.params | enclosing)
        key = kind + ast.dump(gen, include_attributes=False) + repr(self._quantifier_context)
        if key not in self.quantified_functions:
            name = self._fresh("VSpec" + self._mangle(self.node.name))
            args = ", ".join(f"{self._mangle(n)}: {self.types[n]}" for n in captured)
            requirements = [*self._compiled_requirements,
                            *[domain for _, domains in self._quantifier_context for domain in domains]]
            declaration = [f"ghost predicate {name}({args})", *["  requires " + r for r in requirements],
                           "{", "  " + expression, "}"]
            self.quantified_functions[key] = (name, declaration, self._spec_clause_line)
        name = self.quantified_functions[key][0]
        return name + "(" + ", ".join(self._mangle(n) for n in captured) + ")"

    # -- specs -------------------------------------------------------------------------------

    def spec_expr(self, clause: Clause) -> str:
        assert clause.desugared is not None
        tree = ast.parse(clause.desugared, mode="eval")
        self.spec_mode = True
        self._spec_clause_kind = clause.kind
        self._spec_clause_line = clause.line
        try:
            expression = self.expr(tree.body)
            if clause.kind == "requires":
                self._compiled_requirements.append(expression)
            return expression
        except EncodeError as exc:
            raise EncodeError(exc.message, clause.line) from exc
        finally:
            self.spec_mode = False
            self._spec_clause_kind = None

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
                            ann_types[name] = _dafny_type(ann, stmt, self.records)
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
                    case ast.Try(body=body, handlers=handlers, orelse=orelse, finalbody=finalbody):
                        walk(body, path + (idx, "try"))
                        for j,handler in enumerate(handlers):walk(handler.body, path + (idx, "except", j))
                        walk(orelse, path + (idx, "else"))
                        walk(finalbody, path + (idx, "finally"))
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
            if name in self.params or name in loop_indices or name in getattr(self, "_managed_conversion_locals", ()):
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
        self._spec_clause_kind = "proof"
        self._spec_clause_line = clause.line
        try:
            args = ", ".join(self.expr(a) for a in call.args)
        finally:
            self.spec_mode = False
            self._spec_clause_kind = None
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
            # Declare only the new bindings, then perform one simultaneous
            # assignment. Sequential assignments would change swaps and divmod.
            for n, dtype in zip(names, rhs_types):
                if n in fresh:
                    if dtype is None:
                        raise _err(stmt, "cannot infer the new tuple-assignment binding type")
                    self.emit(f"{indent}var {self._mangle(n)}: {dtype};", stmt.lineno)
                    self._declare(n)
                    self.types.setdefault(n, dtype)
            self.emit(f"{indent}{lhs} := {rhs};", stmt.lineno)
            for n, value_node in zip(names, rhs_nodes):
                self._update_ownership(n, value_node)

    def _update_ownership(self, name: str, rhs_node: ast.expr | None) -> None:
        """Ownership-lite: fresh allocations are appendable; aliases are not,
        and aliasing a list forfeits the source's ownership too."""
        # An owned list escaping through a tuple/list/conditional must lose
        # ownership too, not only a direct `alias = xs` binding. Conservative
        # for read-only subexpressions; callers can keep such reads in specs.
        if rhs_node is not None and "seq<" in (self._infer(rhs_node) or ""):
            for n in ast.walk(rhs_node):
                if isinstance(n, ast.Name) and self._is_seqish(self.types.get(n.id)):
                    self.owned.discard(n.id)
        if isinstance(rhs_node, (ast.List, ast.ListComp)) or (rhs_node is not None and self._literal_repeat(rhs_node)):
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
        if self._has_helper(expr):
            if any(isinstance(n, ast.NamedExpr) for n in ast.walk(expr)):
                raise _err(expr, "mixing helper calls and walrus expressions is outside the fragment")
            return self._lower_helpers(expr, indent)
        self._reject_walrus_context(expr)
        stripped, bindings = self._strip_walruses(expr)
        self._emit_walrus_bindings(bindings, indent, stmt)
        return stripped

    def _has_helper(self, node: ast.AST) -> bool:
        return any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                   and n.func.id in self.helpers for n in ast.walk(node))

    def _capture_scalar(self, node: ast.expr, indent: str, want: str | None = None, *, readonly_input=False) -> ast.expr:
        """Evaluate now, including partial-operation VCs, before later calls."""
        got = self._infer(node)
        if want is None and isinstance(node, ast.Constant) and node.value is None:
            return node  # only used by Optional equality / identity comparisons
        dtype = want or got
        if not (_scalar_type(dtype) or readonly_input and dtype is not None and (dtype.startswith("seq<") or dtype.startswith("VRec"))):
            raise _err(node, "helper argument/operand needs a supported value type")
        is_none = isinstance(node, ast.Constant) and node.value is None
        if not (got == dtype or (_opt_inner(dtype) is not None and
                                (got == _opt_inner(dtype) or is_none)) or
                (_opt_inner(got) is not None and _opt_inner(got) == dtype)):
            raise _err(node, f"helper argument type {got!r} does not match {dtype!r}")
        temp = self._fresh("call_value")
        self.emit(f"{indent}var {temp}: {dtype} := {self._coerce(node, dtype)};", node.lineno)
        self.types[temp] = dtype
        return ast.copy_location(ast.Name(id=temp, ctx=ast.Load()), node)

    def _lower_helpers(self, node: ast.expr, indent: str) -> ast.expr:
        """A-normalize only eager scalar contexts, preserving Python order.

        Capturing *all* earlier operands matters: hoisting just method calls
        would reorder division/index failures relative to later calls.
        Unsupported conditional and repeated evaluation fails closed.
        """
        if not self._has_helper(node):
            return node
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in self.helpers:
            sig = self.helpers[node.func.id]
            a = sig.node.args
            positional = [p.arg for p in (*a.posonlyargs, *a.args)]
            posonly = {p.arg for p in a.posonlyargs}
            types = dict(sig.parameters)
            if len(node.args) > len(positional) or any(isinstance(v, ast.Starred) for v in node.args):
                raise _err(node, "invalid helper positional argument binding")
            # CPython evaluates positional expressions, then keyword values
            # in written order, even when keywords reorder the formals.
            bindings: list[tuple[str, ast.expr]] = list(zip(positional, node.args))
            bound = {name for name, _ in bindings}
            for kw in node.keywords:
                if kw.arg is None or kw.arg not in types or kw.arg in posonly or kw.arg in bound:
                    raise _err(node, "invalid helper keyword argument binding")
                bound.add(kw.arg)
                bindings.append((kw.arg, kw.value))
            for name, default in _checked_defaults(sig.node).items():
                if name not in bound:
                    bindings.append((name, default)); bound.add(name)
            if bound != types.keys():
                raise _err(node, "missing helper arguments")
            values: dict[str, ast.expr] = {}
            for name, expr in bindings:
                lowered = self._lower_helpers(expr, indent)
                values[name] = self._capture_scalar(lowered, indent, types[name], readonly_input=True)
            args = ", ".join(self.expr(values[name]) for name, _ in sig.parameters)
            temp = self._fresh("call_result")
            self.emit(f"{indent}var {temp}: {sig.returns};", node.lineno)
            if sig.outcome:
                if not hasattr(self, "_emit_error"):raise _err(node, "outcome helper requires an outcome caller")
                error = self._fresh("call_error")
                self.emit(f"{indent}var {error}: int;")
                self.emit(f"{indent}{temp}, {error} := {self._mangle(node.func.id)}({args});", node.lineno)
                self.emit(f"{indent}if {error} != 0 {{")
                self._emit_error(error, indent + "  ")
                self.emit(f"{indent}}}")
            else:
                self.emit(f"{indent}{temp} := {self._mangle(node.func.id)}({args});", node.lineno)
            self.types[temp] = sig.returns
            if sig.returns.startswith("seq<"):
                # A sequence result may alias any sequence argument. Never
                # grant ownership to it or retain ownership of possible aliases.
                self.owned.clear()
            return ast.copy_location(ast.Name(id=temp, ctx=ast.Load()), node)
        result = copy.copy(node)
        if isinstance(node, ast.BinOp):
            result.left = self._capture_scalar(self._lower_helpers(node.left, indent), indent)
            result.right = self._capture_scalar(self._lower_helpers(node.right, indent), indent)
        elif isinstance(node, ast.UnaryOp):
            result.operand = self._capture_scalar(self._lower_helpers(node.operand, indent), indent)
        elif isinstance(node, ast.BoolOp):
            if any(self._infer(value) != "bool" for value in node.values):
                raise _err(node,"short-circuit helper operands must be boolean")
            first=self._lower_helpers(node.values[0],indent)
            temp=self._fresh("short_circuit")
            self.emit(f"{indent}var {temp}: bool := {self.expr(first)};")
            self.types[temp]="bool"
            for operand in node.values[1:]:
                self.emit(f"{indent}if {temp if isinstance(node.op,ast.And) else '!'+temp} {{")
                value=self._lower_helpers(operand,indent+"  ")
                self.emit(f"{indent}  {temp} := {self.expr(value)};")
                self.emit(f"{indent}}}")
            return ast.copy_location(ast.Name(id=temp,ctx=ast.Load()),node)
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in {"bool", "str"} and len(node.args) == 1 and not node.keywords:
            result.args = [self._capture_scalar(self._lower_helpers(node.args[0], indent), indent)]
        elif isinstance(node, ast.Compare) and len(node.ops) > 1:
            left=self._capture_scalar(self._lower_helpers(node.left,indent),indent)
            temp=self._fresh("comparison_chain")
            self.emit(f"{indent}var {temp}: bool := false;");self.types[temp]="bool"
            def step(index,left,where):
                right=self._capture_scalar(self._lower_helpers(node.comparators[index],where),where)
                comparison=ast.copy_location(ast.Compare(left=left,ops=[node.ops[index]],comparators=[right]),node)
                if index==len(node.ops)-1:self.emit(f"{where}{temp} := {self.expr(comparison)};")
                else:
                    self.emit(f"{where}if {self.expr(comparison)} {{")
                    step(index+1,right,where+"  ")
                    self.emit(f"{where}}}")
            step(0,left,indent)
            return ast.copy_location(ast.Name(id=temp,ctx=ast.Load()),node)
        elif isinstance(node, ast.Compare) and len(node.ops) == 1:
            result.left = self._capture_scalar(self._lower_helpers(node.left, indent), indent)
            result.comparators = [self._capture_scalar(self._lower_helpers(node.comparators[0], indent), indent)]
        else:
            raise _err(node, "helper calls require eager scalar expressions; conditional, container and builtin-call contexts are outside the fragment")
        return result

    def _bool_ctx(self, test: ast.expr) -> str:
        """Encode an expression used as a condition; §7.3 truthiness for
        list/str operands."""
        if isinstance(test, ast.Call):
            model=regex_strings.call_model(self,test)
            if model is not None and model[0] in {"PyOpt<VRegexMatch>","PyOpt<VCharsetCapture>"}:return f"({model[1]}).PySome?"
        if self._infer(test) in {"PyOpt<VRegexMatch>","PyOpt<VCharsetCapture>"}:return f"({self.expr(test)}).PySome?"
        if checksum_sequences.element(self._infer(test)):
            return f"|({self.expr(test)}).VChecksumValues| != 0"
        if self._is_seqish(self._infer(test)):
            return f"(|{self.expr(test)}| != 0)"
        if _is_tuple(self._infer(test)):
            return f"(var {self._fresh('tuple_truth')} := {self.expr(test)}; true)"
        if _is_tuple(_opt_inner(self._infer(test))):
            return f"!({self.expr(test)}).PyNone?"
        if self._infer(test) in {'PyOpt<string>','PyOpt<bool>'}:
            value=self.expr(test)
            inner=f'|({value}).v| != 0' if self._infer(test)=='PyOpt<string>' else f'({value}).v'
            return f'(({value}).PySome? && {inner})'
        if _opt_inner(self._infer(test)) is not None:
            raise _err(test, (
                "truthiness on an Optional conflates None with falsy values "
                "(0, empty) — write `is None` / `is not None` explicitly"
            ))
        t = self._eff_type(test)
        if t == "int":
            return f"({self._deopt(test)} != 0)"
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
        if _is_tuple(want) and isinstance(node,ast.Tuple):
            elems=_tuple_elems(want)
            if len(elems)!=len(node.elts):raise _err(node,'tuple arity mismatch')
            return '('+', '.join(self._coerce(e,t) for e,t in zip(node.elts,elems))+')'
        want_inner = _opt_inner(want)
        if want_inner is not None:
            if isinstance(node, ast.Constant) and node.value is None:
                return "PyNone"
            got = self._infer(node)
            if got == want:
                return self.expr(node)
            return f"PySome({self._coerce(node, want_inner)})"
        got = self._infer(node)
        if want == "string" and got == "char":
            return f"[{self.expr(node)}]"
        if _opt_inner(got) == want:
            return f"({self.expr(node)}).v"
        return self.expr(node)

    def _key_sorted(self, node, indent):
        if not (len(node.args) == 1 and len(node.keywords) == 1 and node.keywords[0].arg == "key"
                and isinstance(node.args[0], ast.Call) and isinstance(node.args[0].func, ast.Name)
                and node.args[0].func.id == "range" and len(node.args[0].args) == 1 and not node.args[0].keywords
                and isinstance(node.keywords[0].value, ast.Lambda)):
            raise _err(node, "keyed sorting supports range(n) with a pure integer tuple key")
        key = node.keywords[0].value
        if len(key.args.args) != 1 or key.args.posonlyargs or key.args.kwonlyargs or key.args.defaults or key.args.vararg or key.args.kwarg or not isinstance(key.body, ast.Tuple) or not key.body.elts:
            raise _err(node, "sorting key requires one argument and a nonempty tuple")
        raw = key.args.args[0].arg
        if raw in self.types or raw in self.name_overrides or _preamble_clash(raw):
            raise _err(node, "sorting key binder must be fresh")
        if self._has_helper(node) or any(isinstance(n, ast.NamedExpr) for n in ast.walk(node)):
            raise _err(node, "sorting keys must be pure and cannot call executable helpers")
        n = node.args[0].args[0]
        if self._infer(n) != "int":
            raise _err(node, "range length must be an integer")
        count = self._fresh("sort_count")
        self.emit(f"{indent}var {count} := PyMax(0, {self.expr(n)});", node.lineno)
        binder = self._fresh("sort_index")
        self.types[raw] = "int"; self.name_overrides[raw] = binder
        try:
            chunks = []
            for elt in key.body.elts:
                if isinstance(elt, ast.Starred) and isinstance(elt.value, ast.GeneratorExp):
                    gen = elt.value
                    if len(gen.generators) != 1 or not isinstance(gen.generators[0].target, ast.Name) or gen.generators[0].is_async:
                        raise _err(elt, "key expansion requires one pure integer generator")
                    chunks.append(self._list_comp(gen, gen.elt, gen.generators[0], require_int_elt=True))
                elif self._infer(elt) == "int":
                    chunks.append("["+self.expr(elt)+"]")
                else:
                    raise _err(elt, "sorting keys contain only integers and integer generator expansions")
            # The first component must exist so the proof can expose primary ordering.
            if isinstance(key.body.elts[0], ast.Starred):
                raise _err(key.body, "sorting key requires an explicit first integer")
            primary = self.expr(key.body.elts[0])
        finally:
            self.types.pop(raw, None); self.name_overrides.pop(raw, None)
        keys = self._fresh("sort_keys")
        self.emit(f"{indent}var {keys}: seq<seq<int>> := seq({count}, {binder} requires 0 <= {binder} < {count} => {' + '.join(chunks)});", node.lineno)
        self.emit(f"{indent}PySortIndexFacts(0, {keys});", node.lineno)
        self.emit(f"{indent}PySortIndexPrimary({keys}, seq({count}, {binder} requires 0 <= {binder} < {count} => {primary}));", node.lineno)
        return f"PySortIndexFrom(0, {keys})"

    def stmt(self, stmt: ast.stmt, indent: str) -> None:
        header = stmt.test if isinstance(stmt, ast.While) else stmt.iter if isinstance(stmt, ast.For) else None
        if header is not None and self._has_helper(header):
            raise _err(header, "helper calls in loop headers are outside the fragment")
        for clause in self._proofs_by_stmt.pop(id(stmt), []):
            self._emit_proof(clause, indent)
        match stmt:
            case ast.Assign(targets=[ast.Name(id=name)], value=ast.Call(func=ast.Name(id="sorted")) as call) if call.keywords:
                value = self._key_sorted(call, indent)
                self._assign_name(name, value, indent, stmt, ann="seq<int>")
                # Use checked contracts after sorting; recursive definitions
                # otherwise trigger unbounded unfolding in later quantified loops.
                self.emit(f"{indent}hide PySortIndexFrom, PyInsertIndex, PyLexSeq, PyInsert2;")
                return
            case ast.Expr(value=ast.Call(func=ast.Name(id=name), args=[ast.Name(id=target), value], keywords=[])) if self.sequence_imports.get(name) == "insort" and name not in self._shadowed:
                if target not in self.owned or target in self.frozen or self.types.get(target) != "seq<(int, int)>" or self._infer(value) != "(int, int)":
                    raise _err(stmt, "insort requires an owned, unaliased integer-pair list outside its iteration")
                seq, item = self._mangle(target), self.expr(value)
                self.emit(f"{indent}PyInsert2Facts({item}, {seq});", stmt.lineno)
                self.emit(f"{indent}{seq} := PyInsert2({item}, {seq});", stmt.lineno)
                return
            case ast.Delete(targets=[ast.Subscript(value=ast.Name(id=name), slice=ast.Slice(lower=None, upper=upper, step=None))]) if upper is not None:
                if name not in self.owned or name in self.frozen or not (self.types.get(name) or "").startswith("seq<") or self._infer(upper) != "int":
                    raise _err(stmt, "prefix deletion requires an owned list outside its iteration and an integer bound")
                seq = self._mangle(name)
                self.emit(f"{indent}{seq} := PySlice({seq}, {self.expr(upper)}, |{seq}|);", stmt.lineno)
                return
            case ast.Expr(value=ast.Constant(value=str())):
                return  # docstring
            case ast.Pass():
                return
            case ast.Expr(value=ast.NamedExpr() as value):
                self._emit_walruses(value, indent, stmt)
                return
            case ast.Expr(value=ast.Call(func=ast.Attribute(value=ast.Name(id=target), attr="sort"), args=[], keywords=[])):
                if target not in self.owned or target in self.frozen:
                    raise _err(stmt, "sort requires an owned, unaliased list outside its iteration")
                dtype = self.types.get(target)
                arity = {"seq<(int, int)>": 2, "seq<(int, int, int)>": 3}.get(dtype)
                if arity is None:
                    raise _err(stmt, "list.sort supports integer pairs/triples without options")
                name = self._mangle(target)
                self.emit(f"{indent}PySorted{arity}Facts({name});", stmt.lineno)
                self.emit(f"{indent}{name} := PySorted{arity}({name});", stmt.lineno)
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
                dtype = _dafny_type(ann, stmt, self.records)
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
            case ast.AugAssign(target=ast.Subscript(value=ast.Name(id=name), slice=index), op=ast.Mult(), value=value):
                if name not in self.owned or name in self.frozen or self.types.get(name) != "seq<int>":
                    raise _err(stmt, "element *= requires a fresh unaliased integer list outside its iteration")
                if not isinstance(index, (ast.Name, ast.Constant)) or any(isinstance(n, (ast.Call, ast.NamedExpr)) for n in ast.walk(value)):
                    raise _err(stmt, "element *= requires a simple index and call-free integer RHS")
                # AugAssign reads its target BEFORE evaluating the RHS, unlike
                # ordinary assignment. Capture all operands before the write.
                idx = self._capture_scalar(index, indent, "int")
                read = ast.copy_location(ast.Subscript(value=ast.Name(id=name, ctx=ast.Load()), slice=idx, ctx=ast.Load()), stmt)
                old = self._capture_scalar(read, indent, "int")
                rhs = self._capture_scalar(value, indent, "int")
                target = self._mangle(name)
                self.emit(f"{indent}{target} := {target}[PyIndex({self.expr(idx)}, |{target}|) := {self.expr(old)} * {self.expr(rhs)}];", stmt.lineno)
            case ast.AugAssign(target=ast.Name(id=name), op=op, value=value):
                if name in self.params:
                    raise _err(stmt, "parameter rebinding is outside the fragment (parameters are immutable)")
                value = self._emit_walruses(value, indent, stmt)
                if (self.types.get(name) == "int" and isinstance(op, ast.Add)
                        and isinstance(value, (ast.Name, ast.Constant)) and self._infer(value) == "bool"):
                    value = ast.copy_location(ast.IfExp(test=value, body=ast.Constant(value=1),
                                                       orelse=ast.Constant(value=0)), value)
                    ast.fix_missing_locations(value)
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
                    safe = isinstance(msg,ast.Name) and self._infer(msg) in {"int","bool","string"}
                    if isinstance(msg,ast.JoinedStr):
                        safe=all(isinstance(p,ast.Constant) and type(p.value) is str or
                                 isinstance(p,ast.FormattedValue) and isinstance(p.value,ast.Name) and self._infer(p.value) in {"int","bool","string"} and p.format_spec is None
                                 for p in msg.values)
                    if not safe:raise _err(stmt, "assert messages require literals or pure scalar formatting (side effects)")
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
            case ast.Assign(targets=[ast.Subscript(value=ast.Name(id=name), slice=index)], value=value) \
                    if not isinstance(index, ast.Slice):
                if any(isinstance(n, ast.NamedExpr) for e in (value, index) for n in ast.walk(e)):
                    raise _err(stmt, "walrus rebinding in indexed writes is outside the fragment", rule="indexed-assignment")
                if name not in self.owned or name in self.frozen:
                    raise _err(stmt, "indexed writes require a fresh, unaliased local list outside its iteration", rule="indexed-assignment")
                dtype = self.types.get(name)
                if dtype is None or not dtype.startswith("seq<") or dtype[4:-1] not in {"int", "bool", "string"}:
                    raise _err(stmt, "indexed writes currently support scalar list elements only", rule="indexed-assignment")
                # Python evaluates RHS before the target index. Freeze both
                # values before the sequence update; PyIndex emits bounds VCs.
                value = self._emit_walruses(value, indent, stmt)
                rhs = self._capture_scalar(value, indent, dtype[4:-1])
                index = self._emit_walruses(index, indent, stmt)
                idx = self._capture_scalar(index, indent, "int")
                target = self._mangle(name)
                self.emit(f"{indent}{target} := {target}[PyIndex({self.expr(idx)}, |{target}|) := {self.expr(rhs)}];", stmt.lineno)
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
        enumerated = (isinstance(stmt.iter, ast.Call) and isinstance(stmt.iter.func, ast.Name)
                      and stmt.iter.func.id == "enumerate")
        if enumerated and (len(stmt.iter.args) != 1 or stmt.iter.keywords or len(names) != 2):
            raise _err(stmt, "enumerate requires one list and an (index, value) target")
        it = self._emit_walruses(stmt.iter.args[0] if enumerated else stmt.iter, indent, stmt)
        it_type = self._infer(it)
        if not (it_type is not None and it_type.startswith("seq<")):
            raise _err(stmt, "for-each iterables must be list-typed (or use `for i in range(...)`)")
        elem = it_type[4:-1]
        if enumerated:
            bind_types = ["int", elem]
        elif len(names) > 1:
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
        # The hidden cursor, not a Python target, drives this loop. Rebinding
        # an element target therefore does not change iteration order/extent.
        # For enumerate, the index target remains immutable because existing
        # invariants expose it as the hidden cursor.
        if enumerated:
            for n in ast.walk(ast.Module(body=stmt.body, type_ignores=[])):
                if isinstance(n, ast.Name) and n.id == names[0] and isinstance(n.ctx, ast.Store):
                    raise _err(n, "reassigning the enumerate index is outside the fragment")
        for clause in self._invariants_by_loop.get(id(stmt), []):
            if clause.desugared:
                tree = ast.parse(clause.desugared, mode="eval")
                hit = next((v for v in (names[1:] if enumerated else names)
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
        if enumerated:
            self.types[names[0]] = "int"
            self.name_overrides[names[0]] = idx
            self.nonneg.add(names[0])
        previous_cursor = getattr(self, "iteration_cursor", None)
        self.iteration_cursor = idx
        self._loop_clauses(stmt, indent, extra=(f"0 <= {idx} <= |{snap}|",))
        if enumerated:
            self.name_overrides.pop(names[0])
        self.emit(f"{indent}{{")
        if enumerated:
            self.emit(f"{indent}  var {self._mangle(names[0])} := {idx};", stmt.lineno)
            self.emit(f"{indent}  var {self._mangle(names[1])} := {snap}[{idx}];", stmt.lineno)
        elif len(names) == 1:
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
            self.iteration_cursor = previous_cursor
        self.owned &= pre_owned
        self.emit(f"{indent}  {idx} := {idx} + 1;")
        self.emit(f"{indent}}}")
        # The target's post-loop value differs between the languages (last
        # element vs out-of-scope); reject later reads.
        self.retired.update(names)
        if enumerated:
            self.nonneg.discard(names[0])

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
        _checked_defaults(node)
        for p in (*a.posonlyargs, *a.args, *a.kwonlyargs):
            self.types[p.arg] = _dafny_type(p.annotation, p, self.records)
        self.return_type = _dafny_type(node.returns, node, self.records)
        self.hoisted = self._hoist_analysis()
        params = ", ".join(
            f"{self._mangle(p.arg)}: {self.types[p.arg]}"
            for p in (*a.posonlyargs, *a.args, *a.kwonlyargs)
        )
        # Mutable-list loops combine quantified functional and bounds VCs.
        # Isolating assertions is a prover scheduling choice, not an assumption
        # or a change to the generated executable semantics.
        isolate = "{:isolate_assertions} " if any(
            (isinstance(n, ast.Assign) and any(isinstance(t, ast.Subscript) for t in n.targets))
            or (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "bisect_right")
            for n in ast.walk(node)) else ""
        if self.spec.by_kind("ghost_ensures"):isolate = "{:isolate_assertions} "
        self.emit(f"method {isolate}{self._mangle(node.name)}({params}) returns (result: {self.return_type})", node.lineno)
        for clause in self.spec.by_kind("requires"):
            self.emit(f"  requires {self.spec_expr(clause)}", clause.line)
        for clause in self.spec.by_kind("ensures"):
            self.emit(f"  ensures {self.spec_expr(clause)}", clause.line)
        for clause in self.spec.by_kind("ghost_ensures"):
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
    method_names: dict[str, str] = field(default_factory=dict)


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


_NESTED_SCOPE = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)


def _walk_skip_def_bodies(node: ast.AST):
    """Module-visible nodes: yield nested defs/classes but do not enter them."""
    yield node
    for child in ast.iter_child_nodes(node):
        if isinstance(child, _NESTED_SCOPE):
            yield child
            continue
        yield from _walk_skip_def_bodies(child)


def _alias_copy_from(target: ast.expr, value: ast.expr, aliases: set[str]) -> list[str]:
    """Names in `target` that this assignment binds to a math-module alias."""
    if isinstance(target, ast.Name) and isinstance(value, ast.Name) \
            and value.id in aliases:
        return [target.id]
    if isinstance(target, (ast.Tuple, ast.List)) \
            and isinstance(value, (ast.Tuple, ast.List)) \
            and len(target.elts) == len(value.elts) \
            and not any(isinstance(e, ast.Starred) for e in target.elts):
        names: list[str] = []
        for t, v in zip(target.elts, value.elts):
            names.extend(_alias_copy_from(t, v, aliases))
        return names
    return []


def _collect_math_imports(
    module: ast.Module,
) -> tuple[dict[str, str], frozenset[str], dict[str, str]]:
    """Module-level `math` bindings the encoder uses to resolve calls.

    `math_names` maps a local name to `{gcd,factorial,isqrt}`; `math_aliases`
    is the set of names bound to the `math` module itself; `math_other` maps
    a local name to any other imported `math` attribute (for diagnostics).
    Only unconditional top-level imports bind — a nested `if`/`for`/`try`
    import is not guaranteed to run, and a later module-level Store, Del,
    attribute mutation (`math.gcd = …` / `del math.gcd`), or wildcard
    import, or an assignment that aliases the module (`m = math`) then
    mutates through the copy (`m.gcd = …`) may replace the math meaning.
    Recording those would lower
    `PyGcd`/`PyFact`/`PyIsqrt` for CPython behavior the source does not have.
    Function bodies are out of scope — only module-level imports resolve.
    """
    math_names: dict[str, str] = {}
    aliases: set[str] = set()
    math_other: dict[str, str] = {}

    def unbind(name: str) -> None:
        math_names.pop(name, None)
        aliases.discard(name)
        math_other.pop(name, None)

    def unbind_all() -> None:
        math_names.clear()
        aliases.clear()
        math_other.clear()

    def drop_aliases() -> None:
        # Attribute mutation through any alias is visible on every name
        # bound to the same math module object (`m = math`; `m.gcd = …`
        # replaces `math.gcd`). Drop the whole alias set; `from math
        # import gcd` snapshots the function and stays in math_names.
        aliases.clear()

    def alias_copy_targets(stmt: ast.stmt) -> list[str]:
        """Names this statement binds to an existing math-module alias."""
        value: ast.expr | None = None
        targets: list[ast.expr] = []
        if isinstance(stmt, ast.Assign):
            value, targets = stmt.value, list(stmt.targets)
        elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            value, targets = stmt.value, [stmt.target]
        if value is None:
            return []
        names: list[str] = []
        for t in targets:
            names.extend(_alias_copy_from(t, value, aliases))
        return names

    def take(stmt: ast.stmt) -> None:
        match stmt:
            case ast.Import(names=alist):
                for a in alist:
                    local = a.asname or a.name.split(".")[0]
                    unbind(local)
                    if a.name == "math":
                        aliases.add(local)
            case ast.ImportFrom(names=alist) as im:
                for a in alist:
                    if a.name == "*":
                        unbind_all()
                        continue
                    local = a.asname or a.name
                    unbind(local)
                    if im.module == "math" and not im.level:
                        if a.name in _ADMITTED_MATH:
                            math_names[local] = a.name
                        else:
                            math_other[local] = a.name

    def drop_module_binds(stmt: ast.stmt) -> None:
        copies = alias_copy_targets(stmt)
        for n in _walk_skip_def_bodies(stmt):
            if isinstance(n, _NESTED_SCOPE):
                unbind(n.name)
            elif isinstance(n, (ast.Import, ast.ImportFrom)):
                for a in n.names:
                    if a.name == "*":
                        unbind_all()
                    else:
                        unbind((a.asname or a.name).split(".")[0])
            elif isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
                unbind(n.id)
            elif isinstance(n, ast.Attribute) and isinstance(n.ctx, (ast.Store, ast.Del)):
                # Mutation through any receiver can be an untracked
                # alias of the math module (`m, _ = math, 0`; `m.gcd = …`).
                drop_aliases()
                if isinstance(n.value, ast.Name):
                    unbind(n.value.id)
            elif isinstance(n, ast.ExceptHandler) and n.name:
                unbind(n.name)
            elif isinstance(n, (ast.MatchAs, ast.MatchStar)) and n.name:
                unbind(n.name)
            elif isinstance(n, ast.MatchMapping) and n.rest:
                unbind(n.rest)
        for name in copies:
            aliases.add(name)

    for stmt in module.body:
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            take(stmt)
        elif isinstance(stmt, _NESTED_SCOPE):
            unbind(stmt.name)
        else:
            drop_module_binds(stmt)
    return math_names, frozenset(aliases), math_other


def _sequence_imports(module):
    result = {}
    for n in module.body:
        if isinstance(n, ast.Import) and any(a.name == "sys" for a in n.names):
            if len(n.names) != 1 or n.names[0].asname:
                raise _err(n, "sys import must be unaliased")
            result["sys"] = "sys"
        elif isinstance(n, ast.ImportFrom) and n.module == "bisect":
            if n.level or any(a.asname or a.name not in {"bisect_right", "insort"} for a in n.names):
                raise _err(n, "bisect imports permit only unaliased bisect_right and insort")
            result.update((a.name,a.name) for a in n.names)
    if result:
        for n in module.body:
            if isinstance(n, (ast.Import, ast.ImportFrom)):
                for a in n.names:
                    bound = (a.asname or a.name).split(".")[0]
                    if a.name == "*":
                        raise _err(n, "star imports can shadow sequence intrinsics")
                    expected = (isinstance(n, ast.Import) and a.name == "sys" and not a.asname
                                or isinstance(n, ast.ImportFrom) and n.module == "bisect"
                                and n.level == 0 and a.name in {"bisect_right", "insort"} and not a.asname)
                    if bound in result and not expected:
                        raise _err(n, "import shadows a sequence intrinsic")
                continue
            if isinstance(n, ast.ClassDef) and n.name not in result:
                continue
            if isinstance(n, ast.FunctionDef) and n.name not in result:
                continue
            if isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant) and isinstance(n.value.value, str):
                continue
            raise _err(n, "sequence intrinsics require a closed module without rebinding")
    return result

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
    from veripy.backends.dafny.environment import resolve_for_encoder, EnvironmentError
    try:
        environment = resolve_for_encoder(module)
    except EnvironmentError as exc:
        raise EncodeError(exc.message, exc.line, "module-environment") from exc
    module = environment.module
    from veripy.frontend.fixed_loops import lower_fixed_loops
    module = lower_fixed_loops(module, specs)
    math_names, math_aliases, math_other = _collect_math_imports(module)
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
    try:
        records = record_schemas(module)
    except RecordError as exc:
        raise EncodeError(str(exc), exc.line) from exc
    if records:
        specified_names = {s.name for s in specs.functions}
        for node in module.body:
            if isinstance(node, ast.FunctionDef) and node.name not in specified_names:
                raise _err(node, "all functions in a record module must be explicitly specified")
    helpers = _helper_signatures(module, specs, records)
    from veripy.backends.dafny import http_lists
    try:
        http_models = http_lists.imports(module)
        percent_models = percent_decoding.imports(module)
    except ValueError as exc:raise EncodeError(str(exc), None) from exc
    header = [
        f"// Generated by `veripy verify` -- DO NOT EDIT the stub (source: {module_name})",
        "// Proof additions belong below the STUB END marker (additions-only discipline).",
        "",
        *PREAMBLE.splitlines(),
        *(unicode_strings.preamble().splitlines() if unicode_strings.needed(module) or environment.regex_models else []),
        *(regex_strings.PREAMBLE.splitlines() if environment.regex_models else []),
        *(http_lists.PREAMBLE.splitlines() if http_models else []),
        *(percent_decoding.PREAMBLE.splitlines() if percent_models else []),
        "",
    ]
    for name, fields in records.items():
        args = ", ".join(f"{record_field(f)}: {_dafny_type(t, t, records)}" for f, t in fields)
        header.append(f"datatype {record_type(name)} = {record_constructor(name)}({args})")
    lines: list[str] = list(header)
    line_map: dict[int, int] = {}
    methods: list[str] = []
    method_names: dict[str, str] = {}
    reserved_names = frozenset(
        n.id if isinstance(n, ast.Name) else n.arg if isinstance(n, ast.arg) else n.name
        for n in ast.walk(module) if isinstance(n, (ast.Name, ast.arg, ast.FunctionDef))
    )
    encoders: list[_MethodEncoder] = []
    for spec in specs.functions:
        node = functions.get((spec.name, spec.lineno))
        if node is None:
            raise EncodeError(f"cannot locate function {spec.name!r}", spec.lineno)
        node, spec = _localize_scalar_parameters(node, spec, reserved_names)
        enc = _MethodEncoder(
            node, spec, proof_lemmas, source_lines=source.split("\n"),
            math_names=math_names, math_aliases=math_aliases,
            math_other=math_other, reserved_names=reserved_names, helpers=helpers, records=records,
            sequence_imports=_sequence_imports(module), module_values=environment.values, regex_models=environment.regex_models, newtypes=environment.newtypes, casts=environment.casts, exceptions=environment.exceptions,
        )
        encoders.append(enc)
    # Callee references and definitions must use the same mapping, including
    # collisions introduced only by another function's proof annotations.
    if helpers:
        all_names = set().union(*(enc.used_names for enc in encoders))
        for enc in encoders:
            enc.used_names.update(all_names)
            enc.mangle_map = enc._build_mangle_map()
    for enc in encoders:
        spec = enc.spec
        enc.encode()
        method_names[spec.name] = enc._mangle(spec.name)
        offset = len(lines)
        lines.extend(enc.lines)
        lines.append("")
        for idx, py_line in enc.line_map.items():
            line_map[offset + idx + 1] = py_line  # 1-based dafny lines
        methods.append(spec.name)
        for _, declaration, py_line in enc.quantified_functions.values():
            for declaration_line in declaration:
                lines.append(declaration_line)
                line_map[len(lines)] = py_line
            lines.append("")
    lines.append("// ---- STUB END: proof additions (lemmas, asserts) go below ----")
    return EncodedModule("\n".join(lines) + "\n", line_map, methods, method_names)
