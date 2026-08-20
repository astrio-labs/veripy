"""The versioned Dafny preamble (ARCHITECTURE §7.1) — Python-exact arithmetic.

Inlined into every emitted stub so stubs are self-contained. `PyMod`/
`PyFloorDiv` implement Python's floor-based semantics on top of Dafny's
Euclidean operators; they coincide exactly when the divisor is positive.

The divisibility lemma pack (needed for e.g. gcd's maximality ensures, which
times out without it) is designated future preamble work — see ROADMAP.
"""

import re

PREAMBLE_VERSION = "0.7"

PREAMBLE = """\
// VeriPy Dafny preamble v0.7 -- Python-exact arithmetic, indexing,
// slicing, Optionals, folds, powers, outcomes, filtered comprehensions,
// ASCII-faithful str methods (ARCHITECTURE §7.1, §7 catalog).
// PyMod/PyFloorDiv: Python floor-based // and % on Dafny's Euclidean ops.
function PyMod(a: int, b: int): int
  requires b != 0
{
  if b < 0 && a % b != 0 then a % b + b else a % b
}

function PyFloorDiv(a: int, b: int): int
  requires b != 0
{
  (a - PyMod(a, b)) / b
}

function PyMin(a: int, b: int): int { if a <= b then a else b }
function PyMax(a: int, b: int): int { if a >= b then a else b }
function PyAbs(a: int): int { if a >= 0 then a else -a }

// Python index normalization: s[i] with -|s| <= i < 0 means s[|s| + i].
// The requires clause is exactly Python's IndexError condition.
function PyIndex(i: int, n: int): int
  requires -n <= i < n
{
  if i < 0 then i + n else i
}

// Optional[T] / T | None. Narrowing is replayed as VCs: using `.v` carries
// the well-formedness obligation PySome?, discharged by `is None` guards.
datatype PyOpt<T> = PyNone | PySome(v: T)

// Python slice s[lo:hi] (step 1): both bounds clamp, negatives count from
// the end, and an inverted range is empty -- exactly Python's semantics.
function PySlice<T>(s: seq<T>, lo: int, hi: int): seq<T>
{
  var n := |s|;
  var l := if lo < 0 then PyMax(0, n + lo) else if lo < n then lo else n;
  var h := if hi < 0 then PyMax(0, n + hi) else if hi < n then hi else n;
  if l >= h then [] else s[l..h]
}

// max()/min() over a nonempty int list; the requires is exactly Python's
// ValueError condition for an empty sequence.
function PySeqMax(s: seq<int>): int
  requires |s| >= 1
  decreases |s|
{
  if |s| == 1 then s[0] else PyMax(PySeqMax(s[..|s|-1]), s[|s|-1])
}

function PySeqMin(s: seq<int>): int
  requires |s| >= 1
  decreases |s|
{
  if |s| == 1 then s[0] else PyMin(PySeqMin(s[..|s|-1]), s[|s|-1])
}

// sum() over an int list; total, and sum([]) == 0, exactly Python.
// Snoc-recursive so loop invariants over growing prefixes step with the
// slice-extension fact (`xs[:i+1] == xs[:i] + [xs[i]]`) alone.
function PySum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else PySum(s[..|s|-1]) + s[|s|-1]
}

// Flatten a seq of parts. Filtered list comprehensions lower to
// seq(n, i => if P then [e] else []) — a seq of 0/1-element seqs —
// and this concatenates them in order, matching CPython's one-pass skip.
function PyFlatten<T>(parts: seq<seq<T>>): seq<T>
  decreases |parts|
{
  if |parts| == 0 then [] else PyFlatten(parts[..|parts|-1]) + parts[|parts|-1]
}

// x ** e for ints; Python yields a float for negative exponents, so the
// requires is exactly the int fragment's domain condition.
function PyPow(b: int, e: int): int
  requires e >= 0
  decreases e
{
  if e == 0 then 1 else b * PyPow(b, e - 1)
}

// Exceptions as VALUES (ARCHITECTURE §7.4). A function that can raise
// returns PyOutcome<T> instead of T, so "this call can fail" is visible in
// the type and provable in a postcondition:
//     ensures b == 0 ==> result == PyErr(ZeroDivisionError)
// The hierarchy is explicit and finite on purpose: `except` matches
// against these constructors, and a bare `except`/`BaseException` would
// claim to catch failures the model does not represent.
datatype PyExn = ValueError | IndexError | ZeroDivisionError | TypeError | KeyError

// IsFailure/PropagateFailure/Extract must be MEMBERS, not free functions:
// that is exactly what makes the datatype failure-compatible, so a caller
// can write `var x :- f(a);` and get Python's propagate-on-raise for free.
// Declared free, every `:-` site fails resolution with an error pointing
// at the call rather than the declaration.
datatype PyOutcome<T> = PyOk(value: T) | PyErr(exn: PyExn)
{
  predicate IsFailure() { this.PyErr? }
  function PropagateFailure<U>(): PyOutcome<U>
    requires IsFailure()
  { PyErr(this.exn) }
  function Extract(): T
    requires !IsFailure()
  { this.value }
}

// str methods, CPython-faithful on the admitted domain (exact substring
// match / char membership). Unicode-table methods (lower/upper/isdigit,
// no-arg strip/split) are encoder rejections — an ASCII A-Z rewrite
// would be a silent approximation.
// Empty needle: s.find("") == 0, including on "".
function PyStrFind(s: string, sub: string): int
  decreases |s|
{
  if |sub| == 0 then 0
  else if |s| < |sub| then -1
  else if s[..|sub|] == sub then 0
  else
    var rest := PyStrFind(s[1..], sub);
    if rest < 0 then -1 else rest + 1
}

function PyStrJoin(sep: string, parts: seq<string>): string
  decreases |parts|
{
  if |parts| == 0 then ""
  else if |parts| == 1 then parts[0]
  else parts[0] + sep + PyStrJoin(sep, parts[1..])
}

// Unlimited split on a nonempty sep. Empty s → [""]; consecutive seps
// yield empty parts. The encoder rejects a visible empty sep; the
// requires is the ValueError condition for a non-literal empty.
function PyStrSplit(s: string, sep: string): seq<string>
  requires |sep| >= 1
  ensures |PyStrSplit(s, sep)| >= 1
  decreases |s|
{
  if |s| < |sep| then
    [s]
  else if s[..|sep|] == sep then
    [""] + PyStrSplit(s[|sep|..], sep)
  else
    var rest := PyStrSplit(s[1..], sep);
    [s[..1] + rest[0]] + rest[1..]
}

function PyStrStartsWith(s: string, prefix: string): bool
{
  |prefix| <= |s| && s[..|prefix|] == prefix
}

function PyStrEndsWith(s: string, suffix: string): bool
{
  |suffix| <= |s| && s[|s| - |suffix|..] == suffix
}

// Non-overlapping left-to-right replace. Empty `pat` is Python's
// insert-between-chars (rejected by the encoder); the requires is that
// domain condition for a non-literal old. Parameter names avoid Dafny
// keywords `old` / `new`.
function PyStrReplace(s: string, pat: string, repl: string): string
  requires |pat| >= 1
  decreases |s|
{
  if |s| < |pat| then s
  else if s[..|pat|] == pat then repl + PyStrReplace(s[|pat|..], pat, repl)
  else s[..1] + PyStrReplace(s[1..], pat, repl)
}

function PyStrLStrip(s: string, chars: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if s[0] in chars then PyStrLStrip(s[1..], chars)
  else s
}

function PyStrRStrip(s: string, chars: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if s[|s| - 1] in chars then PyStrRStrip(s[..|s| - 1], chars)
  else s
}

function PyStrStrip(s: string, chars: string): string
{
  PyStrRStrip(PyStrLStrip(s, chars), chars)
}
"""


# Names the preamble occupies in the emitted stub's top-level scope: every
# column-0 declaration, plus the constructors a datatype injects into the
# enclosing scope. An encoded Python name that lands on one of these is a
# duplicate Dafny declaration (or, for a local or binder, a use that
# resolves to the wrong thing), and the user sees a resolver error against
# generated Dafny instead of a fragment rejection -- so the encoder reserves
# this set. Derived from the preamble TEXT, not restated by hand: a
# declaration added to a later preamble is reserved the moment it is
# written, and cannot reopen the hole by being forgotten here.
# Datatype members (IsFailure/PropagateFailure/Extract) are deliberately not
# in the set -- they are reached only through a receiver, so a Python name
# equal to one of them cannot collide.
_DECL = re.compile(
    r"^(?:function|predicate|method|lemma|datatype|codatatype|newtype|type"
    r"|const|class|trait|iterator)\s+(?:\{:[^}]*\}\s*)*"
    r"([A-Za-z_?'][A-Za-z0-9_?']*)",
    re.MULTILINE,
)
_DATATYPE_RHS = re.compile(
    r"^(?:co)?datatype\s+\w+(?:<[^>]*>)?\s*=\s*(.*)$", re.MULTILINE)
_CTOR = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)")


def _top_level_names(text: str) -> frozenset[str]:
    names = set(_DECL.findall(text))
    for rhs in _DATATYPE_RHS.findall(text):
        for alternative in rhs.split("|"):
            ctor = _CTOR.match(alternative)
            if ctor:
                names.add(ctor.group(1))
    return frozenset(names)


PREAMBLE_NAMES = _top_level_names(PREAMBLE)
