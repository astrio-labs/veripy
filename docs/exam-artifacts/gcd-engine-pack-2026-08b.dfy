lemma LemmaEuclidUnique(n: int, d: int, q: int, r: int)
  requires d >= 1
  requires 0 <= r < d
  requires n == d * q + r
  ensures n % d == r
  ensures n / d == q
{
  var q2 := n / d;
  var r2 := n % d;
  assert n == d * q2 + r2;
  assert 0 <= r2 < d;
  assert d * q + r == d * q2 + r2;
  assert d * q - d * q2 == r2 - r;
  assert d * (q - q2) == d * q - d * q2;
  assert d * (q - q2) == r2 - r;
  if q != q2 {
    if q > q2 {
      assert q - q2 >= 1;
      assert q - q2 - 1 >= 0;
      assert d * (q - q2 - 1) >= 0;
      assert d * (q - q2) == d * (q - q2 - 1) + d;
      assert d * (q - q2) >= d;
      assert false;
    } else {
      assert q2 - q >= 1;
      assert q2 - q - 1 >= 0;
      assert d * (q2 - q - 1) >= 0;
      assert d * (q2 - q) == d * (q2 - q - 1) + d;
      assert d * (q2 - q) >= d;
      assert d * (q - q2) == -(d * (q2 - q));
      assert d * (q - q2) <= -d;
      assert false;
    }
  }
  assert q == q2;
  assert r == r2;
}

lemma ModMulAdd(m: int, r: int, d: int)
  requires d >= 1
  ensures (d * m + r) % d == r % d
{
  var r0 := r % d;
  var rq := r / d;
  assert r == d * rq + r0;
  assert 0 <= r0 < d;
  assert d * (m + rq) == d * m + d * rq;
  assert d * m + r == d * (m + rq) + r0;
  LemmaEuclidUnique(d * m + r, d, m + rq, r0);
}

lemma PyModPos(n: int, d: int)
  requires d >= 1
  ensures PyMod(n, d) == n % d
{
  assert d * (n / d) + n % d == n;
  assert 0 <= n % d < d;
  ModMulAdd(1, n % d, d);
  assert d * 1 + n % d == (n % d) + d;
  assert (n % d) % d == n % d;
  assert ((n % d) + d) % d == n % d;
}

lemma EuclidStepMod(x: int, y: int, d: int)
  requires y >= 1 && d >= 1
  ensures (y % d == 0 && (x % y) % d == 0) == (x % d == 0 && y % d == 0)
{
  if y % d == 0 {
    var q := x / y;
    var r := x % y;
    var e := y / d;
    assert y == d * e;
    assert x == y * q + r;
    assert y * q == (d * e) * q;
    assert (d * e) * q == d * (e * q);
    assert x == d * (e * q) + r;
    ModMulAdd(e * q, r, d);
    assert (d * (e * q) + r) % d == r % d;
    assert x % d == r % d;
  }
}

lemma EuclidStepAll(x: int, y: int, bound: int)
  requires y >= 1
  ensures forall d :: 1 <= d < bound ==>
      ((PyMod(y, d) == 0 && PyMod(PyMod(x, y), d) == 0) ==
       (PyMod(x, d) == 0 && PyMod(y, d) == 0))
{
  forall d | 1 <= d < bound
    ensures (PyMod(y, d) == 0 && PyMod(PyMod(x, y), d) == 0) ==
            (PyMod(x, d) == 0 && PyMod(y, d) == 0)
  {
    PyModPos(y, d);
    PyModPos(x, d);
    PyModPos(x, y);
    var r := x % y;
    assert PyMod(x, y) == r;
    PyModPos(r, d);
    assert PyMod(PyMod(x, y), d) == r % d;
    EuclidStepMod(x, y, d);
  }
}
