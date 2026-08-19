// VeriPy Dafny preamble v0.5 -- Python-exact arithmetic, indexing,
// slicing, Optionals, folds, powers (ARCHITECTURE §7.1, §7 catalog).
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

// --- slice 8 probe: raising functions as Outcome<T>, `:-` propagation ---

datatype PyExn = ValueError | IndexError | ZeroDivisionError
// Dafny's elephant operator requires these as MEMBERS of the datatype,
// not free functions — that is what makes PyOutcome failure-compatible.
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

// def checked_div(a, b): if b == 0: raise ZeroDivisionError; return a // b
method checked_div(a: int, b: int) returns (result: PyOutcome<int>)
  ensures b == 0 ==> result == PyErr(ZeroDivisionError)
  ensures b != 0 ==> result == PyOk(PyFloorDiv(a, b))
{
  if b == 0 { return PyErr(ZeroDivisionError); }
  return PyOk(PyFloorDiv(a, b));
}

// A CALLER that propagates: `x = checked_div(a, b)` with no try/except.
method ratio_sum(a: int, b: int, c: int) returns (result: PyOutcome<int>)
  ensures b == 0 || c == 0 ==> result.PyErr?
  ensures b != 0 && c != 0 ==>
            result == PyOk(PyFloorDiv(a, b) + PyFloorDiv(a, c))
{
  var x :- checked_div(a, b);   // propagation for free
  var y :- checked_div(a, c);
  return PyOk(x + y);
}

// A caller that HANDLES: try/except ZeroDivisionError -> default.
method safe_div(a: int, b: int, fallback: int) returns (result: int)
  ensures b == 0 ==> result == fallback
  ensures b != 0 ==> result == PyFloorDiv(a, b)
{
  var o := checked_div(a, b);
  match o {
    case PyErr(e) => 
      if e == ZeroDivisionError { return fallback; }
      else { return fallback; }   // other exns: no other raiser here
    case PyOk(v) => return v;
  }
}
