// ---- proof additions from task.proofs.dfy ----

lemma PyModToMod(a: int, b: int)
  requires a >= 0
  requires b > 0
  ensures PyMod(a, b) == a % b
{
}

lemma MulComm(a: int, b: int)
  requires a >= 0
  ensures a * b == b * a
  decreases a
{
  if a == 0 {
    assert a * b == 0;
    assert b * a == 0;
  } else {
    MulComm(a - 1, b);
    assert a * b == (a - 1) * b + b;
    assert b * a == b * (a - 1) + b;
  }
}

lemma MulMod(a: int, b: int)
  requires a >= 0
  requires b > 0
  ensures (a * b) % b == 0
  decreases a
{
  if a == 0 {
    assert 0 * b == 0;
  } else {
    MulMod(a - 1, b);
    assert a * b == (a - 1) * b + b;
  }
}

lemma MulMonoLeft(z: int, x: int, y: int)
  requires z >= 0
  requires x <= y
  ensures z * x <= z * y
  decreases z
{
  if z == 0 {
    assert 0 * x == 0;
    assert 0 * y == 0;
  } else {
    MulMonoLeft(z - 1, x, y);
    assert z * x == (z - 1) * x + x;
    assert z * y == (z - 1) * y + y;
  }
}

lemma DivMulExact(n: int, d: int)
  requires n >= 0
  requires d > 0
  requires n % d == 0
  ensures n == d * (n / d)
  ensures n / d >= 0
{
  var q := n / d;
  assert n == q * d + n % d;
  assert n == q * d;
  assert q >= 0;
  MulComm(q, d);
  assert q * d == d * q;
  assert n == d * q;
}

lemma CompositeHasSmallFactor(n: int, k: int)
  requires 2 <= k
  requires n >= 2
  requires k * k > n
  requires forall j :: 2 <= j < k ==> PyMod(n, j) != 0
  ensures forall d :: 2 <= d < n ==> PyMod(n, d) != 0
{
  forall d | 2 <= d < n
    ensures PyMod(n, d) != 0
  {
    PyModToMod(n, d);
    if n % d == 0 {
      DivMulExact(n, d);
      var e := n / d;
      assert n == d * e;
      assert e >= 0;

      if e == 0 {
        assert d * e == d * 0;
        assert d * 0 == 0;
        assert n == 0;
        assert false;
      }
      if e == 1 {
        assert d * e == d * 1;
        assert d * 1 == d;
        assert n == d;
        assert false;
      }
      assert e >= 2;

      MulMod(d, e);
      assert (d * e) % e == 0;
      assert n % e == 0;

      if d < k {
        assert 2 <= d < k;
        assert PyMod(n, d) != 0;
        assert PyMod(n, d) == n % d;
        assert false;
      } else if e < k {
        assert 2 <= e < k;
        PyModToMod(n, e);
        assert PyMod(n, e) != 0;
        assert PyMod(n, e) == n % e;
        assert false;
      } else {
        assert k <= d;
        assert k <= e;
        MulMonoLeft(k, k, e);
        assert k * k <= k * e;
        MulComm(k, e);
        assert k * e == e * k;
        MulMonoLeft(e, k, d);
        assert e * k <= e * d;
        MulComm(e, d);
        assert e * d == d * e;
        assert k * k <= d * e;
        assert d * e == n;
        assert k * k <= n;
        assert false;
      }
    }
  }
}
