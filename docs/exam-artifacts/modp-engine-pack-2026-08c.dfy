lemma PowStepTwo(i: int)
  requires i >= 0
  ensures PyPow(2, i + 1) == 2 * PyPow(2, i)
{
}

lemma PyModIsEuclid(a: int, p: int)
  requires p >= 1
  ensures PyMod(a, p) == a % p
{
  assert 0 <= a % p < p;
  assert a % p + p == p * 1 + a % p;
  assert (a % p + p) % p == a % p;
}

lemma ModPlusP(z: int, p: int)
  requires p >= 1
  ensures (z + p) % p == z % p
{
}

lemma ModMinusP(z: int, p: int)
  requires p >= 1
  ensures (z - p) % p == z % p
{
}

lemma AddMulMod(y: int, q: int, p: int)
  requires p >= 1
  ensures (y + q * p) % p == y % p
  decreases if q >= 0 then q else -q
{
  if q == 0 {
  } else if q > 0 {
    calc {
      (y + q * p) % p;
      == { assert q * p == (q - 1) * p + p; }
        ((y + (q - 1) * p) + p) % p;
      == { ModPlusP(y + (q - 1) * p, p); }
        (y + (q - 1) * p) % p;
      == { AddMulMod(y, q - 1, p); }
        y % p;
    }
  } else {
    calc {
      (y + q * p) % p;
      == { assert q * p == (q + 1) * p - p; }
        ((y + (q + 1) * p) - p) % p;
      == { ModMinusP(y + (q + 1) * p, p); }
        (y + (q + 1) * p) % p;
      == { AddMulMod(y, q + 1, p); }
        y % p;
    }
  }
}

lemma ModMulNative(a: int, b: int, p: int)
  requires p >= 1
  ensures (b * (a % p)) % p == (b * a) % p
{
  var d := a / p;
  var m := a % p;
  assert a == d * p + m;
  assert b * a == b * (d * p + m);
  assert b * (d * p + m) == b * m + (b * d) * p;
  AddMulMod(b * m, b * d, p);
  assert (b * a) % p == (b * m) % p;
}

lemma ModMulLeft(a: int, b: int, p: int)
  requires p >= 1
  ensures PyMod(b * PyMod(a, p), p) == PyMod(b * a, p)
{
  PyModIsEuclid(a, p);
  PyModIsEuclid(b * PyMod(a, p), p);
  PyModIsEuclid(b * a, p);
  ModMulNative(a, b, p);
}
