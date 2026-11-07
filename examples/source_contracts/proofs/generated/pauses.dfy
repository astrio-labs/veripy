// Generated outcome model from pauses.py
// VeriPy Dafny preamble v0.8 -- Python-exact arithmetic, indexing,
// slicing, Optionals, folds, powers, gcd/factorial/isqrt, int/str parse,
// outcomes, filtered comprehensions, sorted and ASCII-faithful str methods (ARCHITECTURE §7.1, §7 catalog).
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
  ensures 0 <= PyIndex(i,n) < n
  ensures i >= 0 ==> PyIndex(i,n) == i
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

// Unlimited non-overlapping str.count(sub); the empty substring occurs at
// all |s|+1 boundaries. No start/end or implicit Unicode normalization.
function PyStrCount(s: string, sub: string): nat
  decreases |s|
{
  if |sub| == 0 then |s| + 1
  else if |s| < |sub| then 0
  else if s[..|sub|] == sub then 1 + PyStrCount(s[|sub|..], sub)
  else PyStrCount(s[1..], sub)
}

// x ** e for ints; Python yields a float for negative exponents, so the
// requires is exactly the int fragment's domain condition.
function PyPow(b: int, e: int): int
  requires e >= 0
  decreases e
{
  if e == 0 then 1 else b * PyPow(b, e - 1)
}

// math.gcd: nonnegative GCD of two ints; gcd(0, 0) == 0; gcd(-a, b) == gcd(a, b).
// Euclidean % on the absolute values; decreases |b|.
function PyGcd(a: int, b: int): int
  ensures PyGcd(a, b) >= 0
  decreases PyAbs(b)
{
  if b == 0 then PyAbs(a) else PyGcd(PyAbs(b), PyAbs(a) % PyAbs(b))
}

// math.factorial: 0! == 1; requires n >= 0 is Python's ValueError domain.
function PyFact(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * PyFact(n - 1)
}

// math.isqrt: floor(sqrt(n)). Logarithmic via isqrt(n) = 2*isqrt(n/4) or +1
// — never recurse n times (Hypothesis ints would blow the stack).
function PyIsqrt(n: int): int
  requires n >= 0
  decreases n
{
  if n <= 1 then n
  else
    var small := PyIsqrt(n / 4) * 2;
    var large := small + 1;
    if large * large > n then small else large
}

// str(n) / int(s). Recursion is O(digits). The parse domain is tight:
// optional ASCII minus, then a nonempty string of ASCII digits 0-9.
// No leading '+', no underscores, no whitespace, no 0x/0b/0o, no empty,
// no "-" alone. int("08") == 8 (default int() is not octal); int("-0") == 0.
// PyIsIntStr is exactly Python's ValueError condition on that domain.
function PyDigit(n: nat): char
  requires n <= 9
{
  (('0' as int) + n) as char
}

function PyNatToStr(n: nat): string
  decreases n
{
  if n < 10 then [PyDigit(n)]
  else PyNatToStr(n / 10) + [PyDigit(n % 10)]
}

function PyIntToStr(n: int): string
{
  if n >= 0 then PyNatToStr(n as nat)
  else "-" + PyNatToStr((-n) as nat)
}

predicate PyIsDigits(s: string)
{
  |s| >= 1 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate PyIsIntStr(s: string)
{
  if |s| == 0 then false
  else if s[0] == '-' then PyIsDigits(s[1..])
  else PyIsDigits(s)
}

function PyDigitsToNat(s: string): nat
  requires PyIsDigits(s)
  decreases |s|
{
  if |s| == 1 then (s[0] as int - '0' as int) as nat
  else PyDigitsToNat(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int) as nat
}

function PyStrToInt(s: string): int
  requires PyIsIntStr(s)
{
  if s[0] == '-' then -(PyDigitsToNat(s[1..]) as int)
  else PyDigitsToNat(s) as int
}

// sorted(xs) on list[int]: insertion sort. Equal ints are
// indistinguishable, so stability is free on this domain. No key= /
// reverse= / list[str] — those stay rejected (Dafny seq < is prefix
// order, Python str < is lex).
function PyInsert(x: int, s: seq<int>): seq<int>
  decreases |s|
{
  if s == [] then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + PyInsert(x, s[1..])
}

function PySorted(s: seq<int>): seq<int>
  decreases |s|
{
  if s == [] then []
  else PyInsert(s[0], PySorted(s[1..]))
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

// Unlike slicing, affix matching must not clamp a positive start to |s|.
// An empty affix fails when start exceeds the string or the normalized end.
function PyStrStartsWithRange(s: string, prefix: string, start: int, end: int): bool
{
  var lo := if start < 0 then PyMax(0, |s| + start) else start;
  var hi := if end < 0 then PyMax(0, |s| + end) else PyMin(end, |s|);
  lo <= hi && PyStrStartsWith(PySlice(s, lo, hi), prefix)
}

function PyStrEndsWithRange(s: string, suffix: string, start: int, end: int): bool
{
  var lo := if start < 0 then PyMax(0, |s| + start) else start;
  var hi := if end < 0 then PyMax(0, |s| + end) else PyMin(end, |s|);
  lo <= hi && PyStrEndsWith(PySlice(s, lo, hi), suffix)
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

function PyProd(s: seq<int>): int
  decreases |s|
{ if |s| == 0 then 1 else PyProd(s[..|s|-1]) * s[|s|-1] }

predicate PyLex2(a: (int, int), b: (int, int)) { (a.0 < b.0) || (a.0 == b.0 && a.1 <= b.1) }
function PyInsert2(x: (int, int), s: seq<(int, int)>): seq<(int, int)>
  decreases |s|
{ if |s| == 0 then [x] else if PyLex2(x,s[0]) then [x] + s else [s[0]] + PyInsert2(x,s[1..]) }
function PySorted2(s: seq<(int, int)>): seq<(int, int)>
  decreases |s|
{ if |s| == 0 then [] else PyInsert2(s[0], PySorted2(s[1..])) }
lemma PyInsert2Facts(x: (int, int), s: seq<(int, int)>)
  requires forall i,j :: 0 <= i < j < |s| ==> PyLex2(s[i], s[j])
  ensures |PyInsert2(x,s)| == |s| + 1
  ensures forall v :: v in PyInsert2(x,s) <==> v == x || v in s
  ensures multiset(PyInsert2(x,s)) == multiset(s) + multiset{x}
  ensures forall i,j :: 0 <= i < j < |PyInsert2(x,s)| ==> PyLex2(PyInsert2(x,s)[i], PyInsert2(x,s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    if !PyLex2(x,s[0]) {
      PyInsert2Facts(x,s[1..]);
      var tail := PyInsert2(x,s[1..]);
      forall k | 0 <= k < |tail| ensures PyLex2(s[0],tail[k]) {
        if tail[k] != x {
          assert tail[k] in tail;
          assert multiset(tail)[tail[k]] > 0;
          assert multiset{x}[tail[k]] == 0;
          assert tail[k] in s[1..];
          var j :| 0 <= j < |s[1..]| && s[1..][j] == tail[k];
          assert PyLex2(s[0],s[j+1]);
        }
      }
    } else {
      forall j | 0 <= j < |s| ensures PyLex2(x,s[j]) {
        if j > 0 { assert PyLex2(s[0],s[j]); }
      }
    }
  }
}
lemma PySorted2Facts(s: seq<(int, int)>)
  ensures |PySorted2(s)| == |s|
  ensures forall v :: v in PySorted2(s) <==> v in s
  ensures multiset(PySorted2(s)) == multiset(s)
  ensures forall i,j :: 0 <= i < j < |PySorted2(s)| ==> PyLex2(PySorted2(s)[i], PySorted2(s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    PySorted2Facts(s[1..]);
    PyInsert2Facts(s[0],PySorted2(s[1..]));
  }
}
predicate PyLex3(a: (int, int, int), b: (int, int, int)) { (a.0 < b.0) || (a.0 == b.0 && a.1 < b.1) || (a.0 == b.0 && a.1 == b.1 && a.2 <= b.2) }
function PyInsert3(x: (int, int, int), s: seq<(int, int, int)>): seq<(int, int, int)>
  decreases |s|
{ if |s| == 0 then [x] else if PyLex3(x,s[0]) then [x] + s else [s[0]] + PyInsert3(x,s[1..]) }
function PySorted3(s: seq<(int, int, int)>): seq<(int, int, int)>
  decreases |s|
{ if |s| == 0 then [] else PyInsert3(s[0], PySorted3(s[1..])) }
lemma PyInsert3Facts(x: (int, int, int), s: seq<(int, int, int)>)
  requires forall i,j :: 0 <= i < j < |s| ==> PyLex3(s[i], s[j])
  ensures |PyInsert3(x,s)| == |s| + 1
  ensures forall v :: v in PyInsert3(x,s) <==> v == x || v in s
  ensures multiset(PyInsert3(x,s)) == multiset(s) + multiset{x}
  ensures forall i,j :: 0 <= i < j < |PyInsert3(x,s)| ==> PyLex3(PyInsert3(x,s)[i], PyInsert3(x,s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    if !PyLex3(x,s[0]) {
      PyInsert3Facts(x,s[1..]);
      var tail := PyInsert3(x,s[1..]);
      forall k | 0 <= k < |tail| ensures PyLex3(s[0],tail[k]) {
        if tail[k] != x {
          assert tail[k] in tail;
          assert multiset(tail)[tail[k]] > 0;
          assert multiset{x}[tail[k]] == 0;
          assert tail[k] in s[1..];
          var j :| 0 <= j < |s[1..]| && s[1..][j] == tail[k];
          assert PyLex3(s[0],s[j+1]);
        }
      }
    } else {
      forall j | 0 <= j < |s| ensures PyLex3(x,s[j]) {
        if j > 0 { assert PyLex3(s[0],s[j]); }
      }
    }
  }
}
lemma PySorted3Facts(s: seq<(int, int, int)>)
  ensures |PySorted3(s)| == |s|
  ensures forall v :: v in PySorted3(s) <==> v in s
  ensures multiset(PySorted3(s)) == multiset(s)
  ensures forall i,j :: 0 <= i < j < |PySorted3(s)| ==> PyLex3(PySorted3(s)[i], PySorted3(s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    PySorted3Facts(s[1..]);
    PyInsert3Facts(s[0],PySorted3(s[1..]));
  }
}

predicate PyPerm3(a: seq<(int,int,int)>, b: seq<(int,int,int)>) { multiset(a) == multiset(b) }
function PyCount3(s: seq<(int,int,int)>, x: (int,int,int)): nat { multiset(s)[x] }

lemma PyPerm3Facts(a: seq<(int,int,int)>, b: seq<(int,int,int)>)
  requires PyPerm3(a,b)
  ensures |a| == |b|
  ensures forall x :: x in a <==> x in b
  ensures forall x :: PyCount3(a,x) == PyCount3(b,x)
{
  assert multiset(a) == multiset(b);
  assert |a| == |multiset(a)|;
  assert |b| == |multiset(b)|;
  forall x ensures x in a <==> x in b {
    assert (x in a) == (multiset(a)[x] > 0);
    assert (x in b) == (multiset(b)[x] > 0);
  }
}

function PyLexSeq(a: seq<int>, b: seq<int>): bool
  decreases |a| + |b|
{ if |a| == 0 then true else if |b| == 0 then false else if a[0] < b[0] then true else if a[0] > b[0] then false else PyLexSeq(a[1..],b[1..]) }
function PyInsertIndex(x: int, s: seq<int>, keys: seq<seq<int>>): seq<int>
  requires 0 <= x < |keys|
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < |keys|
  ensures forall v :: v in PyInsertIndex(x,s,keys) <==> v == x || v in s
  decreases |s|
{ if |s| == 0 then [x] else if PyLexSeq(keys[x],keys[s[0]]) then [x]+s else [s[0]]+PyInsertIndex(x,s[1..],keys) }
lemma PyInsertIndexBounds(x: int, s: seq<int>, keys: seq<seq<int>>, lower: int)
  requires 0 <= lower <= x < |keys|
  requires forall i :: 0 <= i < |s| ==> lower <= s[i] < |keys|
  ensures forall i :: 0 <= i < |PyInsertIndex(x,s,keys)| ==> lower <= PyInsertIndex(x,s,keys)[i] < |keys|
{
  var r := PyInsertIndex(x,s,keys);
  forall i | 0 <= i < |r| ensures lower <= r[i] < |keys| {
    assert r[i] in r;
    if r[i] != x {
      assert r[i] in s;
      var j :| 0 <= j < |s| && s[j] == r[i];
    }
  }
}
function PySortIndexFrom(lo: int, keys: seq<seq<int>>): seq<int>
  requires 0 <= lo <= |keys|
  ensures forall i :: 0 <= i < |PySortIndexFrom(lo,keys)| ==> lo <= PySortIndexFrom(lo,keys)[i] < |keys|
  decreases |keys| - lo
{ if lo == |keys| then [] else (PyInsertIndexBounds(lo,PySortIndexFrom(lo+1,keys),keys,lo); PyInsertIndex(lo,PySortIndexFrom(lo+1,keys),keys)) }
lemma PyInsertIndexFacts(x: int, s: seq<int>, keys: seq<seq<int>>)
  requires 0 <= x < |keys|
  requires forall k :: 0 <= k < |keys| ==> |keys[k]| > 0
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < |keys|
  requires forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j] && keys[s[i]][0] <= keys[s[j]][0]
  requires x !in s
  ensures |PyInsertIndex(x,s,keys)| == |s|+1
  ensures forall v :: v in PyInsertIndex(x,s,keys) <==> v == x || v in s
  ensures forall i :: 0 <= i < |PyInsertIndex(x,s,keys)| ==> 0 <= PyInsertIndex(x,s,keys)[i] < |keys|
  ensures forall i,j :: 0 <= i < j < |PyInsertIndex(x,s,keys)| ==> PyInsertIndex(x,s,keys)[i] != PyInsertIndex(x,s,keys)[j] && keys[PyInsertIndex(x,s,keys)[i]][0] <= keys[PyInsertIndex(x,s,keys)[j]][0]
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]]+s[1..];
    if PyLexSeq(keys[x],keys[s[0]]) {
      assert keys[x][0] <= keys[s[0]][0];
      forall j | 0 <= j < |s| ensures keys[x][0] <= keys[s[j]][0] {
        if j>0 { assert keys[s[0]][0] <= keys[s[j]][0]; }
      }
    } else {
      PyInsertIndexFacts(x,s[1..],keys);
      var tail := PyInsertIndex(x,s[1..],keys);
      forall j | 0 <= j < |tail| ensures tail[j] != s[0] && keys[s[0]][0] <= keys[tail[j]][0] {
        assert tail[j] in tail;
        if tail[j] != x {
          assert tail[j] in s[1..];
          var k :| 0 <= k < |s[1..]| && s[1..][k] == tail[j];
          assert s[k+1] != s[0];
          assert keys[s[0]][0] <= keys[s[k+1]][0];
        }
      }
    }
  }
}
lemma PySortIndexFacts(lo: int, keys: seq<seq<int>>)
  requires 0 <= lo <= |keys|
  requires forall k :: 0 <= k < |keys| ==> |keys[k]| > 0
  ensures |PySortIndexFrom(lo,keys)| == |keys|-lo
  ensures forall i :: 0 <= i < |PySortIndexFrom(lo,keys)| ==> lo <= PySortIndexFrom(lo,keys)[i] < |keys|
  ensures forall v :: v in PySortIndexFrom(lo,keys) <==> lo <= v < |keys|
  ensures forall i,j :: 0 <= i < j < |PySortIndexFrom(lo,keys)| ==> PySortIndexFrom(lo,keys)[i] != PySortIndexFrom(lo,keys)[j] && keys[PySortIndexFrom(lo,keys)[i]][0] <= keys[PySortIndexFrom(lo,keys)[j]][0]
  decreases |keys|-lo
{
  if lo < |keys| {
    PySortIndexFacts(lo+1,keys);
    var tail := PySortIndexFrom(lo+1,keys);
    assert lo !in tail;
    PyInsertIndexFacts(lo,tail,keys);
  }
}

function PyBisect2(s: seq<(int,int)>, x: (int,int), lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  requires forall i,j :: 0 <= i < j < |s| ==> PyLex2(s[i],s[j])
  ensures lo <= PyBisect2(s,x,lo,hi) <= hi
  ensures forall i :: lo <= i < PyBisect2(s,x,lo,hi) ==> PyLex2(s[i],x)
  ensures forall i :: PyBisect2(s,x,lo,hi) <= i < hi ==> !PyLex2(s[i],x)
  decreases hi-lo
{
  if lo == hi then lo else
  var mid := (lo+hi)/2;
  if PyLex2(s[mid],x) then PyBisect2(s,x,mid+1,hi) else PyBisect2(s,x,lo,mid)
}

lemma PySortIndexPrimary(keys: seq<seq<int>>, primary: seq<int>)
  requires |keys| == |primary|
  requires forall i :: 0 <= i < |keys| ==> |keys[i]| > 0 && keys[i][0] == primary[i]
  ensures forall i :: 0 <= i < |PySortIndexFrom(0,keys)| ==> (forall j :: i+1 <= j < |PySortIndexFrom(0,keys)| ==> PySortIndexFrom(0,keys)[i] != PySortIndexFrom(0,keys)[j] && primary[PySortIndexFrom(0,keys)[i]] <= primary[PySortIndexFrom(0,keys)[j]])
{
  PySortIndexFacts(0,keys);
  var order := PySortIndexFrom(0,keys);
  forall i | 0 <= i < |order|
    ensures forall j :: i+1 <= j < |order| ==> order[i] != order[j] && primary[order[i]] <= primary[order[j]]
  {
    forall j | i+1 <= j < |order|
      ensures order[i] != order[j] && primary[order[i]] <= primary[order[j]]
    { assert keys[order[i]][0] <= keys[order[j]][0]; }
  }
}

datatype VChecksumTuple<T> = VChecksumTupleMake(VChecksumValues: seq<T>)
function VChecksumReverse<T>(s: seq<T>): seq<T> {
  seq(|s|, i requires 0 <= i < |s| => s[|s|-1-i])
}
function VChecksumStep<T>(s: seq<T>, step: int): seq<T>
  requires step > 0
  decreases |s|
{ if |s| == 0 then [] else [s[0]] + VChecksumStep(s[PyMin(step,|s|)..],step) }
function VChecksumStride<T>(s: seq<T>, lo: int, hi: int, step: int): seq<T>
  requires step > 0
{ VChecksumStep(PySlice(s,lo,hi),step) }
function VChecksumIndex(s: string, needle: string): int
  requires PyStrFind(s,needle) >= 0
{ PyStrFind(s,needle) }
// 0.11-outcomes-1-unicode16.0.0-digits4300; CPython decimal syntax, scalar Unicode strings.
function PyDecimalDigit(c: char): int {
  if 48 <= c as int < 58 then c as int - 48
  else if 1632 <= c as int < 1642 then c as int - 1632
  else if 1776 <= c as int < 1786 then c as int - 1776
  else if 1984 <= c as int < 1994 then c as int - 1984
  else if 2406 <= c as int < 2416 then c as int - 2406
  else if 2534 <= c as int < 2544 then c as int - 2534
  else if 2662 <= c as int < 2672 then c as int - 2662
  else if 2790 <= c as int < 2800 then c as int - 2790
  else if 2918 <= c as int < 2928 then c as int - 2918
  else if 3046 <= c as int < 3056 then c as int - 3046
  else if 3174 <= c as int < 3184 then c as int - 3174
  else if 3302 <= c as int < 3312 then c as int - 3302
  else if 3430 <= c as int < 3440 then c as int - 3430
  else if 3558 <= c as int < 3568 then c as int - 3558
  else if 3664 <= c as int < 3674 then c as int - 3664
  else if 3792 <= c as int < 3802 then c as int - 3792
  else if 3872 <= c as int < 3882 then c as int - 3872
  else if 4160 <= c as int < 4170 then c as int - 4160
  else if 4240 <= c as int < 4250 then c as int - 4240
  else if 6112 <= c as int < 6122 then c as int - 6112
  else if 6160 <= c as int < 6170 then c as int - 6160
  else if 6470 <= c as int < 6480 then c as int - 6470
  else if 6608 <= c as int < 6618 then c as int - 6608
  else if 6784 <= c as int < 6794 then c as int - 6784
  else if 6800 <= c as int < 6810 then c as int - 6800
  else if 6992 <= c as int < 7002 then c as int - 6992
  else if 7088 <= c as int < 7098 then c as int - 7088
  else if 7232 <= c as int < 7242 then c as int - 7232
  else if 7248 <= c as int < 7258 then c as int - 7248
  else if 42528 <= c as int < 42538 then c as int - 42528
  else if 43216 <= c as int < 43226 then c as int - 43216
  else if 43264 <= c as int < 43274 then c as int - 43264
  else if 43472 <= c as int < 43482 then c as int - 43472
  else if 43504 <= c as int < 43514 then c as int - 43504
  else if 43600 <= c as int < 43610 then c as int - 43600
  else if 44016 <= c as int < 44026 then c as int - 44016
  else if 65296 <= c as int < 65306 then c as int - 65296
  else if 66720 <= c as int < 66730 then c as int - 66720
  else if 68912 <= c as int < 68922 then c as int - 68912
  else if 68928 <= c as int < 68938 then c as int - 68928
  else if 69734 <= c as int < 69744 then c as int - 69734
  else if 69872 <= c as int < 69882 then c as int - 69872
  else if 69942 <= c as int < 69952 then c as int - 69942
  else if 70096 <= c as int < 70106 then c as int - 70096
  else if 70384 <= c as int < 70394 then c as int - 70384
  else if 70736 <= c as int < 70746 then c as int - 70736
  else if 70864 <= c as int < 70874 then c as int - 70864
  else if 71248 <= c as int < 71258 then c as int - 71248
  else if 71360 <= c as int < 71370 then c as int - 71360
  else if 71376 <= c as int < 71386 then c as int - 71376
  else if 71386 <= c as int < 71396 then c as int - 71386
  else if 71472 <= c as int < 71482 then c as int - 71472
  else if 71904 <= c as int < 71914 then c as int - 71904
  else if 72016 <= c as int < 72026 then c as int - 72016
  else if 72688 <= c as int < 72698 then c as int - 72688
  else if 72784 <= c as int < 72794 then c as int - 72784
  else if 73040 <= c as int < 73050 then c as int - 73040
  else if 73120 <= c as int < 73130 then c as int - 73120
  else if 73552 <= c as int < 73562 then c as int - 73552
  else if 90416 <= c as int < 90426 then c as int - 90416
  else if 92768 <= c as int < 92778 then c as int - 92768
  else if 92864 <= c as int < 92874 then c as int - 92864
  else if 93008 <= c as int < 93018 then c as int - 93008
  else if 93552 <= c as int < 93562 then c as int - 93552
  else if 118000 <= c as int < 118010 then c as int - 118000
  else if 120782 <= c as int < 120792 then c as int - 120782
  else if 120792 <= c as int < 120802 then c as int - 120792
  else if 120802 <= c as int < 120812 then c as int - 120802
  else if 120812 <= c as int < 120822 then c as int - 120812
  else if 120822 <= c as int < 120832 then c as int - 120822
  else if 123200 <= c as int < 123210 then c as int - 123200
  else if 123632 <= c as int < 123642 then c as int - 123632
  else if 124144 <= c as int < 124154 then c as int - 124144
  else if 124401 <= c as int < 124411 then c as int - 124401
  else if 125264 <= c as int < 125274 then c as int - 125264
  else if 130032 <= c as int < 130042 then c as int - 130032
  else -1
}
predicate PyIntSpace(c: char) {
  9 <= c as int <= 13 || c == ' ' || c as int == 133 || c as int == 160 || c as int == 5760 || c as int == 8192 || c as int == 8193 || c as int == 8194 || c as int == 8195 || c as int == 8196 || c as int == 8197 || c as int == 8198 || c as int == 8199 || c as int == 8200 || c as int == 8201 || c as int == 8202 || c as int == 8232 || c as int == 8233 || c as int == 8239 || c as int == 8287 || c as int == 12288
}
function PyIntLStrip(s: string): string
  decreases |s|
{ if |s| > 0 && PyIntSpace(s[0]) then PyIntLStrip(s[1..]) else s }
function PyIntRStrip(s: string): string
  decreases |s|
{ if |s| > 0 && PyIntSpace(s[|s|-1]) then PyIntRStrip(s[..|s|-1]) else s }
function PyIntTrim(s: string): string { PyIntRStrip(PyIntLStrip(s)) }
function PyUnsignedDecimal(s: string): string {
  if |s| > 0 && (s[0] == '+' || s[0] == '-') then s[1..] else s
}
predicate PyDecimalBody(s: string) {
  |s| > 0 && PyDecimalDigit(s[0]) >= 0 && PyDecimalDigit(s[|s|-1]) >= 0 &&
  (forall i :: 0 <= i < |s| ==>
    PyDecimalDigit(s[i]) >= 0 || (s[i] == '_' && 0 < i < |s|-1 &&
      PyDecimalDigit(s[i-1]) >= 0 && PyDecimalDigit(s[i+1]) >= 0))
}
function PyDecimalCount(s: string): nat
  decreases |s|
{ if |s| == 0 then 0 else PyDecimalCount(s[..|s|-1]) + (if PyDecimalDigit(s[|s|-1]) >= 0 then 1 else 0) }
function PyDecimalValue(s: string): int
  decreases |s|
{ if |s| == 0 then 0 else if s[|s|-1] == '_' then PyDecimalValue(s[..|s|-1])
   else PyDecimalValue(s[..|s|-1]) * 10 + PyDecimalDigit(s[|s|-1]) }
opaque function PyTryDecimal(s: string): PyOpt<int>
  ensures |s| == 0 ==> PyTryDecimal(s).PyNone?
{
  var t := PyIntTrim(s);
  var b := PyUnsignedDecimal(t);
  if PyDecimalBody(b) && (4300 == 0 || PyDecimalCount(b) <= 4300)
  then PySome((if |t| > 0 && t[0] == '-' then -1 else 1) * PyDecimalValue(b))
  else PyNone
}

// Exact builtin int bit_length: sign does not contribute a bit.
function NativeBitLengthNat(n: int): int
  requires n >= 0
  ensures NativeBitLengthNat(n) >= 0
  decreases n
{
  if n == 0 then 0 else 1 + NativeBitLengthNat(n / 2)
}
function NativeBitLength(n: int): int
{ NativeBitLengthNat(if n < 0 then -n else n) }
datatype VRecRetryWindow = VMakeRetryWindow(vfieldbase: int, vfieldcap: int)
method RetryWindow_pause(self: VRecRetryWindow, attempt: int) returns (result: int, outcome_error: bool)
  requires ((((self).vfieldbase > 0)) && (((self).vfieldcap >= (self).vfieldbase)))
  requires ((-86399999913600000000) <= (self).vfieldbase && (self).vfieldbase <= 86399999999999999999)
  requires ((-86399999913600000000) <= (self).vfieldcap && (self).vfieldcap <= 86399999999999999999)
  ensures (outcome_error == (attempt < 0))
  ensures ((!(!(outcome_error))) || ((result == (if (attempt == 0) then (self).vfieldbase else PyMin(((self).vfieldbase * 2), (self).vfieldcap)))))
{
  result := 0; outcome_error := false;
  if (attempt < 0) {
    outcome_error := true;
    return;
  }
  if (attempt == 0) {
    result := (self).vfieldbase;
    return;
  }
  if (PyFloorDiv((self).vfieldcap, (self).vfieldbase) < 2) {
    result := (self).vfieldcap;
    return;
  }
  assert -86399999913600000000 <= ((self).vfieldbase * 2) <= 86399999999999999999;
  result := ((self).vfieldbase * 2);
  return;
}

// ---- STUB END: proof additions go below ----
