"""The versioned Dafny preamble (ARCHITECTURE §7.1) — Python-exact arithmetic.

Inlined into every emitted stub so stubs are self-contained. `PyMod`/
`PyFloorDiv` implement Python's floor-based semantics on top of Dafny's
Euclidean operators; they coincide exactly when the divisor is positive.

The divisibility lemma pack (needed for e.g. gcd's maximality ensures, which
times out without it) is designated future preamble work — see ROADMAP.
"""

PREAMBLE_VERSION = "0.3"

PREAMBLE = """\
// LemmaPy Dafny preamble v0.3 -- Python-exact arithmetic, indexing,
// slicing, Optionals (ARCHITECTURE §7.1, §7 catalog).
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
"""
