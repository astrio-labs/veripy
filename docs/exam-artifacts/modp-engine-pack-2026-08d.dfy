lemma PowStepTwo(i: int)
  requires i >= 0
  ensures PyPow(2, i + 1) == 2 * PyPow(2, i)
{
}

lemma PyModStep(y: int, p: int)
  requires p >= 1
  ensures PyMod(y + p, p) == PyMod(y, p)
{
}

lemma PyModAddMul(x: int, k: int, p: int)
  requires p >= 1
  ensures PyMod(x + k * p, p) == PyMod(x, p)
  decreases if k >= 0 then k else -k
{
  if k == 0 {
    assert x + 0 * p == x;
  } else if k > 0 {
    PyModStep(x + (k - 1) * p, p);
    assert (x + (k - 1) * p) + p == x + k * p;
    PyModAddMul(x, k - 1, p);
  } else {
    PyModStep(x + k * p, p);
    assert (x + k * p) + p == x + (k + 1) * p;
    PyModAddMul(x, k + 1, p);
  }
}

// ModMulLeft avoids the div/mod identity (no PyFloorDiv) and any three-way
// multiplicative associativity: it reduces `a` toward its residue in [0, p)
// by single +/- p steps, discharging each step with PyModStep (to shift the
// residue) and PyModAddMul with multiplier `b` (whose added term `b * p` is
// already in `k * p` shape, so only distribution over addition is needed).
lemma ModMulLeft(a: int, b: int, p: int)
  requires p >= 1
  ensures PyMod(b * PyMod(a, p), p) == PyMod(b * a, p)
  decreases if a < 0 then p - a else a
{
  if 0 <= a < p {
    assert PyMod(a, p) == a;
  } else if a >= p {
    PyModStep(a - p, p);
    assert PyMod(a, p) == PyMod(a - p, p);
    assert PyMod(b * PyMod(a, p), p) == PyMod(b * PyMod(a - p, p), p);
    ModMulLeft(a - p, b, p);
    PyModAddMul(b * (a - p), b, p);
    assert b * a == b * (a - p) + b * p;
    assert PyMod(b * a, p) == PyMod(b * (a - p), p);
  } else {
    PyModStep(a, p);
    assert PyMod(a, p) == PyMod(a + p, p);
    assert PyMod(b * PyMod(a, p), p) == PyMod(b * PyMod(a + p, p), p);
    ModMulLeft(a + p, b, p);
    PyModAddMul(b * a, b, p);
    assert b * (a + p) == b * a + b * p;
    assert PyMod(b * (a + p), p) == PyMod(b * a, p);
  }
}
