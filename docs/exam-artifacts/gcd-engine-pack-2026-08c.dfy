lemma ModAddD(a: int, d: int)
  requires d > 0
  ensures (a + d) % d == a % d
{
  assert a == d * (a / d) + a % d;
  assert a + d == d * (a / d + 1) + a % d;
  assert 0 <= a % d < d;
}

lemma ModAddMul(r: int, m: int, d: int)
  requires d > 0
  requires m >= 0
  ensures (r + d * m) % d == r % d
  decreases m
{
  if m == 0 {
    assert r + d * 0 == r;
  } else {
    ModAddMul(r, m - 1, d);
    assert r + d * m == (r + d * (m - 1)) + d;
    ModAddD(r + d * (m - 1), d);
  }
}

lemma PyModNat(n: int, d: int)
  requires n >= 0
  requires d > 0
  ensures PyMod(n, d) == n % d
{
}

lemma EuclidStepOne(x: int, y: int, d: int)
  requires x >= 0
  requires y > 0
  requires d >= 1
  ensures (PyMod(x, d) == 0 && PyMod(y, d) == 0) ==
          (PyMod(y, d) == 0 && PyMod(PyMod(x, y), d) == 0)
{
  PyModNat(x, d);
  PyModNat(y, d);
  PyModNat(x, y);
  PyModNat(x % y, d);
  // After the bridges above:
  //   PyMod(x, d) == x % d
  //   PyMod(y, d) == y % d
  //   PyMod(x, y) == x % y   (a value in [0, y), hence >= 0)
  //   PyMod(x % y, d) == (x % y) % d
  // and therefore PyMod(PyMod(x, y), d) == (x % y) % d.
  if y % d == 0 {
    var qy := x / y;
    var r := x % y;
    var ky := y / d;
    assert ky >= 0;
    assert qy >= 0;
    assert y == d * ky;
    assert x == y * qy + r;
    assert x == r + d * (ky * qy);
    ModAddMul(r, ky * qy, d);
    assert x % d == r % d;
  }
}

lemma EuclidStepAll(x: int, y: int, N: int)
  requires x >= 0
  requires y > 0
  ensures forall d :: 1 <= d < N ==>
    ((PyMod(x, d) == 0 && PyMod(y, d) == 0) ==
     (PyMod(y, d) == 0 && PyMod(PyMod(x, y), d) == 0))
{
  forall d | 1 <= d < N
    ensures (PyMod(x, d) == 0 && PyMod(y, d) == 0) ==
            (PyMod(y, d) == 0 && PyMod(PyMod(x, y), d) == 0)
  {
    EuclidStepOne(x, y, d);
  }
}
