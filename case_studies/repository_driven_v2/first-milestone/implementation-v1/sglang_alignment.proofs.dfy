// Checked ghost support. Euclidean quotient uniqueness supplies the nonlinear
// multiplication fact Z3 does not reliably instantiate from division alone.
lemma NonnegativeProduct(k: int, d: int)
  requires k >= 0 && d >= 0
  ensures k * d >= 0
  decreases k
{
  if k > 0 {
    NonnegativeProduct(k - 1, d);
    assert k * d == (k - 1) * d + d;
  }
}

lemma EuclideanUnique(a: int, b: int, q: int, r: int)
  requires b != 0
  requires 0 <= r < (if b > 0 then b else -b)
  requires a == q * b + r
  ensures a / b == q && a % b == r
{
  var q2 := a / b;
  var r2 := a % b;
  assert a == q2 * b + r2;
  assert (q - q2) * b == r2 - r;
  if q > q2 {
    if b > 0 {
      NonnegativeProduct(q - q2 - 1, b);
      assert (q - q2) * b == (q - q2 - 1) * b + b;
    } else {
      NonnegativeProduct(q - q2 - 1, -b);
      assert (q - q2) * b == -((q - q2 - 1) * (-b)) + b;
    }
  } else if q < q2 {
    if b > 0 {
      NonnegativeProduct(q2 - q - 1, b);
      assert (q2 - q) * b == (q2 - q - 1) * b + b;
    } else {
      NonnegativeProduct(q2 - q - 1, -b);
      assert (q2 - q) * b == -((q2 - q - 1) * (-b)) + b;
    }
  }
}

lemma FloorDivFacts(a: int, b: int)
  requires b != 0
  ensures a == PyFloorDiv(a, b) * b + PyMod(a, b)
  ensures b > 0 ==> 0 <= PyMod(a, b) < b
  ensures b < 0 ==> b < PyMod(a, b) <= 0
  ensures b > 0 ==> PyFloorDiv(a, b) * b <= a < (PyFloorDiv(a, b) + 1) * b
  ensures b < 0 ==> PyFloorDiv(a, b) * b >= a > (PyFloorDiv(a, b) + 1) * b
  ensures PyMod(PyFloorDiv(a, b) * b, b) == 0
{
  var q := a / b;
  var r := a % b;
  assert a == q * b + r;
  if b > 0 || r == 0 {
    assert PyMod(a, b) == r;
    assert a - r == q * b;
    EuclideanUnique(q * b, b, q, 0);
  } else {
    assert PyMod(a, b) == r + b;
    assert a - (r + b) == (q - 1) * b;
    EuclideanUnique((q - 1) * b, b, q - 1, 0);
  }
  EuclideanUnique(PyFloorDiv(a, b) * b, b, PyFloorDiv(a, b), 0);
}

// Quantified arithmetic fact; the caller need not expose a generated temporary.
lemma AlignedMultiples(b: int)
  requires b > 0
  ensures forall q: int :: PyMod(q * b, b) == 0
{
  forall q: int
    ensures PyMod(q * b, b) == 0
  {
    EuclideanUnique(q * b, b, q, 0);
  }
}
