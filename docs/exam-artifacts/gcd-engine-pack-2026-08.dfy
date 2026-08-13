// ---- proof additions from task.proofs.dfy ----
lemma DivModRel(a: int, b: int)
  requires b > 0
  ensures a == b * (a / b) + a % b
  ensures 0 <= a % b < b
{
}

lemma MulMono(d: int, p: int, q: int)
  requires d > 0
  requires p >= q
  ensures d * p >= d * q
  decreases p - q
{
  if p == q {
  } else {
    MulMono(d, p - 1, q);
    assert d * p == d * (p - 1) + d;
  }
}

lemma MulDivZero(m: int, d: int)
  requires d > 0
  ensures (d * m) % d == 0
{
  DivModRel(d * m, d);
  var s := (d * m) / d;
  var r := (d * m) % d;
  assert d * m == d * s + r;
  assert 0 <= r < d;
  assert r == d * m - d * s;
  if m >= s + 1 {
    MulMono(d, m, s + 1);
    assert d * (s + 1) == d * s + d;
    assert d * m >= d * s + d;
    assert r >= d;
    assert false;
  } else if s >= m + 1 {
    MulMono(d, s, m + 1);
    assert d * (m + 1) == d * m + d;
    assert d * s >= d * m + d;
    assert r <= -d;
    assert false;
  } else {
    assert m == s;
    assert d * m == d * s;
    assert r == 0;
  }
}

lemma MulMod(a: int, c: int, d: int)
  requires d > 0
  requires a % d == 0
  ensures (a * c) % d == 0
{
  var k := a / d;
  DivModRel(a, d);
  assert a == d * k;
  assert a * c == d * (k * c);
  MulDivZero(k * c, d);
}

lemma AddMod(u: int, v: int, d: int)
  requires d > 0
  requires u % d == 0
  requires v % d == 0
  ensures (u + v) % d == 0
{
  var ku := u / d;
  var kv := v / d;
  DivModRel(u, d);
  DivModRel(v, d);
  assert u == d * ku;
  assert v == d * kv;
  assert u + v == d * (ku + kv);
  MulDivZero(ku + kv, d);
}

lemma SubMod(u: int, v: int, d: int)
  requires d > 0
  requires u % d == 0
  requires v % d == 0
  ensures (u - v) % d == 0
{
  var ku := u / d;
  var kv := v / d;
  DivModRel(u, d);
  DivModRel(v, d);
  assert u == d * ku;
  assert v == d * kv;
  assert u - v == d * (ku - kv);
  MulDivZero(ku - kv, d);
}

lemma EuclidStepOne(x: int, y: int, d: int)
  requires y > 0
  requires d > 0
  ensures (y % d == 0 && (x % y) % d == 0) == (x % d == 0 && y % d == 0)
{
  var q := x / y;
  var r := x % y;
  DivModRel(x, y);
  assert x == y * q + r;
  assert r == x - y * q;
  if x % d == 0 && y % d == 0 {
    MulMod(y, q, d);
    assert (y * q) % d == 0;
    SubMod(x, y * q, d);
    assert (x - y * q) % d == 0;
    assert r % d == 0;
  }
  if y % d == 0 && r % d == 0 {
    MulMod(y, q, d);
    assert (y * q) % d == 0;
    AddMod(y * q, r, d);
    assert (y * q + r) % d == 0;
    assert x % d == 0;
  }
}

lemma EuclidStepAll(x: int, y: int, n: int)
  requires y > 0
  ensures forall d :: 1 <= d < n ==> ((y % d == 0 && (x % y) % d == 0) == (x % d == 0 && y % d == 0))
{
  forall d | 1 <= d < n
    ensures (y % d == 0 && (x % y) % d == 0) == (x % d == 0 && y % d == 0)
  {
    EuclidStepOne(x, y, d);
  }
}
