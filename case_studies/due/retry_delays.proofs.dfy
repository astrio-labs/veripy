// Checked ghost support. Euclidean quotient uniqueness supplies the nonlinear
// multiplication fact Z3 does not reliably instantiate from division alone.
lemma NonnegativeProduct(k: int, d: int)
  requires k >= 0 && d >= 0
  ensures k * d >= 0
  decreases k
{
  if k > 0 {
    NonnegativeProduct(k - 1, d);
    assert k * d == (k - 1) * d + d;
  }
}

lemma EuclideanUnique(a: int, b: int, q: int, r: int)
  requires b != 0
  requires 0 <= r < (if b > 0 then b else -b)
  requires a == q * b + r
  ensures a / b == q && a % b == r
{
  var q2 := a / b;
  var r2 := a % b;
  assert a == q2 * b + r2;
  assert (q - q2) * b == r2 - r;
  if q > q2 {
    if b > 0 {
      NonnegativeProduct(q - q2 - 1, b);
      assert (q - q2) * b == (q - q2 - 1) * b + b;
    } else {
      NonnegativeProduct(q - q2 - 1, -b);
      assert (q - q2) * b == -((q - q2 - 1) * (-b)) + b;
    }
  } else if q < q2 {
    if b > 0 {
      NonnegativeProduct(q2 - q - 1, b);
      assert (q2 - q) * b == (q2 - q - 1) * b + b;
    } else {
      NonnegativeProduct(q2 - q - 1, -b);
      assert (q2 - q) * b == -((q2 - q - 1) * (-b)) + b;
    }
  }
}

lemma FloorDivFacts(a: int, b: int)
  requires b != 0
  ensures a == PyFloorDiv(a, b) * b + PyMod(a, b)
  ensures b > 0 ==> 0 <= PyMod(a, b) < b
  ensures b < 0 ==> b < PyMod(a, b) <= 0
  ensures b > 0 ==> PyFloorDiv(a, b) * b <= a < (PyFloorDiv(a, b) + 1) * b
  ensures b < 0 ==> PyFloorDiv(a, b) * b >= a > (PyFloorDiv(a, b) + 1) * b
  ensures PyMod(PyFloorDiv(a, b) * b, b) == 0
{
  var q := a / b;
  var r := a % b;
  assert a == q * b + r;
  if b > 0 || r == 0 {
    assert PyMod(a, b) == r;
    assert a - r == q * b;
    EuclideanUnique(q * b, b, q, 0);
  } else {
    assert PyMod(a, b) == r + b;
    assert a - (r + b) == (q - 1) * b;
    EuclideanUnique((q - 1) * b, b, q - 1, 0);
  }
  EuclideanUnique(PyFloorDiv(a, b) * b, b, PyFloorDiv(a, b), 0);
}

// Quantified arithmetic fact; the caller need not expose a generated temporary.
lemma AlignedMultiples(b: int)
  requires b > 0
  ensures forall q: int :: PyMod(q * b, b) == 0
{
  forall q: int
    ensures PyMod(q * b, b) == 0
  {
    EuclideanUnique(q * b, b, q, 0);
  }
}

predicate NativeDelayExact(i: int, m: int, s: int, output: int)
{
  s >= 0 && output == PyMin(i * PyPow(2,s),m)
}

lemma Pow2Positive(n: int)
  requires n >= 0
  ensures PyPow(2,n) > 0
  decreases n
{
  if n > 0 { Pow2Positive(n-1); }
}

lemma Pow2Monotone(a: int, b: int)
  requires 0 <= a <= b
  ensures PyPow(2,a) <= PyPow(2,b)
  decreases b
{
  Pow2Positive(a);
  if a < b {
    Pow2Monotone(a,b-1);
    assert PyPow(2,b) == 2*PyPow(2,b-1);
  }
}

lemma BitLengthBounds(n: int)
  requires n >= 0
  ensures n < PyPow(2,NativeBitLength(n))
  ensures n > 0 ==> NativeBitLength(n) > 0
  ensures n > 0 ==> PyPow(2,NativeBitLength(n)-1) <= n
  decreases n
{
  if n > 0 {
    var h := n / 2;
    BitLengthBounds(h);
    assert n == 2*h+n%2;
    assert 0 <= n%2 < 2;
    assert NativeBitLength(n) == 1+NativeBitLength(h);
    assert PyPow(2,NativeBitLength(n)) == 2*PyPow(2,NativeBitLength(h));
    if h > 0 {
      assert PyPow(2,NativeBitLength(h)) == 2*PyPow(2,NativeBitLength(h)-1);
    }
  }
}

lemma DelayThreshold(i: int, m: int, s: int)
  requires i > 0 && m >= i
  ensures s >= 0 ==> i * PyPow(2,s) > 0
  ensures s >= 0 && s >= NativeBitLength(PyFloorDiv(m,i)) ==> i * PyPow(2,s) >= m
  ensures s >= 0 && s < NativeBitLength(PyFloorDiv(m,i)) ==> i * PyPow(2,s) <= m
{
  if s >= 0 {
    FloorDivFacts(m,i);
    var q := PyFloorDiv(m,i);
    if q < 1 {
      NonnegativeProduct(-q,i);
      assert q*i <= 0;
    }
    assert q >= 1;
    BitLengthBounds(q);
    Pow2Positive(s);
    NonnegativeProduct(PyPow(2,s)-1,i);
    assert i*PyPow(2,s) == i*(PyPow(2,s)-1)+i;
    var k := NativeBitLength(q);
    if s >= k {
      Pow2Monotone(k,s);
      assert PyPow(2,s) >= q+1;
      NonnegativeProduct(PyPow(2,s)-q-1,i);
      assert i*PyPow(2,s)-i*(q+1) == i*(PyPow(2,s)-q-1);
      assert i*PyPow(2,s) >= i*(q+1);
    } else {
      Pow2Monotone(s,k-1);
      assert PyPow(2,s) <= q;
      NonnegativeProduct(q-PyPow(2,s),i);
      assert i*q-i*PyPow(2,s) == i*(q-PyPow(2,s));
      assert i*PyPow(2,s) <= i*q;
    }
  }
}

lemma NativeDelayMonotonic(i: int, m: int, s: int, a: int, b: int)
  requires i > 0 && m >= i && s >= 0
  requires NativeDelayExact(i,m,s,a) && NativeDelayExact(i,m,s+1,b)
  ensures a <= b
{
  Pow2Monotone(s,s+1);
  NonnegativeProduct(PyPow(2,s+1)-PyPow(2,s),i);
  assert i*PyPow(2,s+1)-i*PyPow(2,s) == i*(PyPow(2,s+1)-PyPow(2,s));
}

lemma NativeDelaySaturation(i: int, m: int, s: int, output: int)
  requires i > 0 && m >= i && s >= 0
  requires NativeDelayExact(i,m,s,output)
  requires i*PyPow(2,s) >= m
  ensures output == m
{
}
