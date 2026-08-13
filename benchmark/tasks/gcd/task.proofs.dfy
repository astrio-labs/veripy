// Divisibility lemma pack for greatest_common_divisor (ghost only).
// Invoked from the source via `#@ proof EuclidStepAll(x, y, max(a, b) + 1)`.
// Grounding: MulPositive gives Z3 the nonlinear fact it cannot find alone;
// ModUnique is Euclid-division uniqueness; the rest is divisibility algebra.

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

lemma ModOfMultiple(k: int, d: int)
  requires d >= 1
  ensures (k * d) % d == 0
  decreases if k >= 0 then k else -k
{
  if k > 0 {
    ModOfMultiple(k - 1, d);
    assert k * d == (k - 1) * d + d;
    ModShift((k - 1) * d, d);
  } else if k < 0 {
    ModOfMultiple(k + 1, d);
    assert (k + 1) * d == k * d + d;
    ModShift(k * d, d);
  }
}

lemma DividesRepresentation(a: int, d: int)
  requires d >= 1 && a % d == 0
  ensures a == (a / d) * d
{
}

lemma DividesDiff(a: int, b: int, q: int, d: int)
  requires d >= 1 && a % d == 0 && b % d == 0
  ensures (a - q * b) % d == 0
{
  var ka := a / d;
  var kb := b / d;
  DividesRepresentation(a, d);
  DividesRepresentation(b, d);
  assert q * b == (q * kb) * d;
  assert a - q * b == (ka - q * kb) * d;
  ModOfMultiple(ka - q * kb, d);
}

lemma DividesSum(r: int, b: int, q: int, d: int)
  requires d >= 1 && r % d == 0 && b % d == 0
  ensures (q * b + r) % d == 0
{
  var kr := r / d;
  var kb := b / d;
  DividesRepresentation(r, d);
  DividesRepresentation(b, d);
  assert q * b + r == (q * kb + kr) * d;
  ModOfMultiple(q * kb + kr, d);
}

lemma EuclidStepAll(x: int, y: int, hi: int)
  requires x >= 0 && y > 0
  ensures forall d | 1 <= d < hi ::
    ((PyMod(x, d) == 0 && PyMod(y, d) == 0) == (PyMod(y, d) == 0 && PyMod(PyMod(x, y), d) == 0))
{
  var q := x / y;
  var r := x % y;
  assert x == q * y + r;
  assert PyMod(x, y) == r;
  forall d | 1 <= d < hi
    ensures (PyMod(x, d) == 0 && PyMod(y, d) == 0) == (PyMod(y, d) == 0 && PyMod(r, d) == 0)
  {
    assert PyMod(x, d) == x % d && PyMod(y, d) == y % d && PyMod(r, d) == r % d;
    if x % d == 0 && y % d == 0 {
      DividesDiff(x, y, q, d);
      assert r == x - q * y;
    }
    if y % d == 0 && r % d == 0 {
      DividesSum(r, y, q, d);
      assert x == q * y + r;
    }
  }
}
