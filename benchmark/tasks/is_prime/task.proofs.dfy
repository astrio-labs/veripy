// Divisibility pack for sqrt-bounded primality (ghost only). The keystone
// CompositeHasSmallFactor: if no j in [2, k) divides n and k*k > n, then
// NO d in [2, n) divides n -- a composite's smallest factor is <= sqrt.

lemma MulPositive(k: int, d: int)
  requires k >= 0 && d >= 0
  ensures k * d >= 0
  decreases k
{
  if k > 0 {
    MulPositive(k - 1, d);
    assert k * d == (k - 1) * d + d;
  }
}

lemma MulMono(a: int, b: int, c: int)
  requires a <= b && c >= 0
  ensures c * a <= c * b
  decreases c
{
  if c > 0 {
    MulMono(a, b, c - 1);
    assert c * a == (c - 1) * a + a;
    assert c * b == (c - 1) * b + b;
  }
}

lemma ModUnique(n: int, d: int, q: int, r: int)
  requires d >= 1 && 0 <= r < d && n == q * d + r
  ensures n % d == r
{
  var q2 := n / d;
  var r2 := n % d;
  assert n == q2 * d + r2 && 0 <= r2 < d;
  assert (q - q2) * d == r2 - r;
  if q > q2 {
    MulPositive(q - q2 - 1, d);
    assert (q - q2) * d == (q - q2 - 1) * d + d;
  } else if q < q2 {
    MulPositive(q2 - q - 1, d);
    assert (q2 - q) * d == (q2 - q - 1) * d + d;
    assert (q - q2) * d == -((q2 - q) * d);
  }
}

lemma ModOfMultiple(k: int, d: int)
  requires d >= 1 && k >= 0
  ensures (k * d) % d == 0
{
  MulPositive(k, d);
  ModUnique(k * d, d, k, 0);
}

lemma DividesRepresentation(a: int, d: int)
  requires d >= 1 && a % d == 0
  ensures a == (a / d) * d
{
}

lemma CompositeHasSmallFactor(n: int, k: int)
  requires n >= 2 && k >= 2
  requires k * k > n
  requires forall j | 2 <= j < k :: PyMod(n, j) != 0
  ensures forall d | 2 <= d < n :: PyMod(n, d) != 0
{
  forall d | 2 <= d < n
    ensures PyMod(n, d) != 0
  {
    assert PyMod(n, d) == n % d;
    if n % d == 0 {
      var q := n / d;
      DividesRepresentation(n, d);
      assert n == q * d;
      // q >= 2: q <= 0 makes n <= 0; q == 1 makes n == d < n.
      if q <= 0 {
        MulPositive(-q, d);
        assert (-q) * d == -(q * d);
        assert false;
      }
      assert q >= 1;
      if q == 1 {
        assert n == d;
        assert false;
      }
      assert q >= 2;
      if d < k {
        assert PyMod(n, d) != 0;
        assert false;
      }
      // d >= k: then q < k, and q is a small factor -- contradiction.
      MulMono(k, d, q);         // q * k <= q * d == n < k * k
      if q >= k {
        MulMono(k, q, k);       // k * k <= k * q == q * k -- contradiction
        assert k * q == q * k;
        assert false;
      }
      assert 2 <= q < k;
      ModOfMultiple(d, q);      // (d * q) % q == 0
      assert d * q == q * d;
      assert n % q == 0;
      assert PyMod(n, q) == n % q;
      assert false;             // requires said PyMod(n, q) != 0
    }
  }
}
