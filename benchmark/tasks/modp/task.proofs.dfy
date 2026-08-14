// Proof pack for modp (HumanEval/49): stepping `ret == (2 ** i) % p`
// needs mod-multiplication congruence, grounded exactly like the gcd
// pack (MulPositive -> ModUnique -> ModShift).

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

lemma ModShift(a: int, d: int)
  requires d >= 1
  ensures (a + d) % d == a % d
{
  var q := a / d;
  var r := a % d;
  assert a == q * d + r && 0 <= r < d;
  assert a + d == (q + 1) * d + r;
  ModUnique(a + d, d, q + 1, r);
}

lemma ModAddMultiple(x: int, k: int, p: int)
  requires p >= 1
  ensures (x + k * p) % p == x % p
  decreases if k >= 0 then k else -k
{
  if k > 0 {
    ModAddMultiple(x, k - 1, p);
    assert x + k * p == (x + (k - 1) * p) + p;
    ModShift(x + (k - 1) * p, p);
  } else if k < 0 {
    ModAddMultiple(x, k + 1, p);
    assert x + (k + 1) * p == (x + k * p) + p;
    ModShift(x + k * p, p);
  }
}

lemma ModMulLeft(a: int, b: int, p: int)
  requires p >= 1
  ensures PyMod(a * b, p) == PyMod(PyMod(a, p) * b, p)
{
  var q := a / p;
  var r := a % p;
  assert a == q * p + r;
  assert a * b == r * b + (q * b) * p;
  ModAddMultiple(r * b, q * b, p);
}

lemma PowStepTwo(i: int)
  requires i >= 0
  ensures 2 * PyPow(2, i) == PyPow(2, i + 1)
{
}
