// ---- proof additions from task.proofs.dfy ----
lemma DistribAdd(m: int, k: int, p: int)
  ensures (m + k) * p == m * p + k * p
{
}

lemma DistribSub(a: int, b: int, p: int)
  ensures (a - b) * p == a * p - b * p
{
}

lemma MulDistribR(b: int, u: int, v: int)
  ensures b * (u + v) == b * u + b * v
{
}

lemma MulAssoc(b: int, q: int, p: int)
  ensures b * (q * p) == (b * q) * p
{
}

lemma MulNonneg(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures x * y >= 0
{
}

lemma MulMonoRight(a: int, b: int, p: int)
  requires a <= b && p >= 0
  ensures a * p <= b * p
{
  MulNonneg(b - a, p);   // (b - a) * p >= 0
  DistribSub(b, a, p);   // (b - a) * p == b*p - a*p, hence b*p - a*p >= 0
}

lemma MulZero(d: int, p: int)
  requires p >= 1
  requires -p < d * p < p
  ensures d == 0
{
  if d >= 1 {
    MulMonoRight(1, d, p);   // 1 * p <= d * p
    assert 1 * p == p;
    assert p <= d * p;       // contradicts d * p < p
  } else if d <= -1 {
    MulMonoRight(d, -1, p);  // d * p <= (-1) * p
    assert (-1) * p == -p;
    assert d * p <= -p;      // contradicts d * p > -p
  }
}

lemma ModUnique(y: int, q: int, r: int, p: int)
  requires p >= 1
  requires 0 <= r < p
  requires y == q * p + r
  ensures y % p == r
{
  var qq := y / p;
  var rr := y % p;
  // Dafny knows automatically: y == qq * p + rr and 0 <= rr < p (p >= 1)
  DistribSub(qq, q, p);            // (qq - q) * p == qq*p - q*p
  // qq*p + rr == y == q*p + r, so qq*p - q*p == r - rr
  assert (qq - q) * p == r - rr;
  assert -p < r - rr < p;          // 0 <= r < p and 0 <= rr < p
  assert -p < (qq - q) * p < p;
  MulZero(qq - q, p);              // qq - q == 0
  assert qq == q;
  assert qq * p == q * p;
  // qq*p + rr == q*p + r with qq*p == q*p forces rr == r
}

lemma LemmaAddMulMod(x: int, k: int, p: int)
  requires p >= 1
  ensures (x + k * p) % p == x % p
{
  var r := x % p;
  var m := x / p;
  // Dafny knows x == m * p + r with 0 <= r < p (p >= 1)
  DistribAdd(m, k, p);
  // (m + k) * p == m * p + k * p, hence x + k * p == (m + k) * p + r
  ModUnique(x + k * p, m + k, r, p);
}

lemma ModMulNative(a: int, b: int, p: int)
  requires p >= 1
  ensures (b * (a % p)) % p == (b * a) % p
{
  var r := a % p;
  var q := a / p;
  // a == q * p + r (known automatically)
  MulDistribR(b, q * p, r);   // b * (q * p + r) == b * (q * p) + b * r
  MulAssoc(b, q, p);          // b * (q * p) == (b * q) * p
  // therefore b * a == b * r + (b * q) * p
  LemmaAddMulMod(b * r, b * q, p);
}

lemma ModMulLeft(a: int, b: int, p: int)
  requires p >= 1
  ensures PyMod(b * PyMod(a, p), p) == PyMod(b * a, p)
{
  assert PyMod(a, p) == a % p;
  assert PyMod(b * PyMod(a, p), p) == (b * (a % p)) % p;
  assert PyMod(b * a, p) == (b * a) % p;
  ModMulNative(a, b, p);
}

lemma PowStepTwo(i: int)
  requires i >= 0
  ensures PyPow(2, i + 1) == 2 * PyPow(2, i)
{
}
