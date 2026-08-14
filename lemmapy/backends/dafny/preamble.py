"""The versioned Dafny preamble (ARCHITECTURE §7.1) — Python-exact arithmetic.

Inlined into every emitted stub so stubs are self-contained. `PyMod`/
`PyFloorDiv` implement Python's floor-based semantics on top of Dafny's
Euclidean operators; they coincide exactly when the divisor is positive.

The divisibility lemma pack (needed for e.g. gcd's maximality ensures, which
times out without it) is designated future preamble work — see ROADMAP.
"""

PREAMBLE_VERSION = "0.6"

PREAMBLE = """\
// LemmaPy Dafny preamble v0.6 -- Python-exact arithmetic, indexing,
// slicing, Optionals, folds, powers, outcomes (ARCHITECTURE §7.1, §7 catalog).
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
"""
