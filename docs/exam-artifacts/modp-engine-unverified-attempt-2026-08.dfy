// ---- proof additions from task.proofs.dfy ----
lemma ModIdentity(a: int, p: int)
  requires p >= 1
  ensures a == p * PyFloorDiv(a, p) + PyMod(a, p)
  ensures 0 <= PyMod(a, p) < p
{
}

lemma MulNonneg(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures x * y >= 0
  decreases y
{
  if y > 0 {
    MulNonneg(x, y - 1);
    assert x * y == x * (y - 1) + x;
  }
}

lemma ModPeriodic(x: int, k: int, p: int)
  requires p >= 1
  ensures PyMod(p * k + x, p) == PyMod(x, p)
{
  ModIdentity(x, p);
  ModIdentity(p * k + x, p);
  var r1 := PyMod(x, p);
  var r2 := PyMod(p * k + x, p);
  assert x == p * PyFloorDiv(x, p) + r1;
  assert p * k + x == p * PyFloorDiv(p * k + x, p) + r2;
  var m := PyFloorDiv(p * k + x, p) - PyFloorDiv(x, p) - k;
  calc {
    p * m;
    ==
    p * PyFloorDiv(p * k + x, p) - p * PyFloorDiv(x, p) - p * k;
    ==
    (p * k + x - r2) - (x - r1) - p * k;
    ==
    r1 - r2;
  }
  assert -p < p * m < p;
  if m > 0 {
    MulNonneg(p, m - 1);
    assert p * (m - 1) >= 0;
    assert p * m == p * (m - 1) + p;
    assert p * m >= p;
    assert false;
  }
  if m < 0 {
    MulNonneg(p, - m - 1);
    assert p * (- m - 1) >= 0;
    assert p * (- m) == p * (- m - 1) + p;
    assert p * (- m) >= p;
    assert p * m == - (p * (- m));
    assert p * m <= -p;
    assert false;
  }
  assert m == 0;
  assert p * m == 0;
  assert r1 - r2 == 0;
}

lemma ModMulLeft(a: int, b: int, p: int)
  requires p >= 1
  ensures PyMod(b * PyMod(a, p), p) == PyMod(b * a, p)
  ensures 0 <= PyMod(b * a, p) < p
  ensures 0 <= PyMod(b * PyMod(a, p), p) < p
{
  ModIdentity(a, p);
  ModIdentity(b * a, p);
  ModIdentity(b * PyMod(a, p), p);
  var q := PyFloorDiv(a, p);
  var r := PyMod(a, p);
  assert a == p * q + r;
  calc {
    b * a;
    ==
    b * (p * q + r);
    ==
    b * (p * q) + b * r;
    ==
    p * (b * q) + b * r;
  }
  ModPeriodic(b * r, b * q, p);
  assert PyMod(b * a, p) == PyMod(b * r, p);
}

lemma PowStepTwo(i: int)
  requires i >= 0
  ensures PyPow(2, i + 1) == 2 * PyPow(2, i)
{
}
