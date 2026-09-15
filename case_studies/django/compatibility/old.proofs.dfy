function Digits(n: int): string
  requires n >= 0
  ensures |Digits(n)| > 0
  decreases n
{
  var chars := "0123456789abcdefghijklmnopqrstuvwxyz";
  if n < 36 then [chars[n]] else Digits(n/36)+[chars[n%36]]
}

predicate EncodingProgress(original: int, remaining: int, suffix: string)
{ original >= 0 && remaining >= 0 && Digits(original) == (if remaining == 0 then suffix else Digits(remaining)+suffix) }

lemma EncodingStep(original: int, remaining: int, suffix: string, chars: string)
  requires remaining > 0
  requires EncodingProgress(original,remaining,suffix)
  requires chars == "0123456789abcdefghijklmnopqrstuvwxyz"
  ensures EncodingProgress(original,remaining/36,[chars[remaining%36]]+suffix)
{
  assert Digits(remaining) == (if remaining < 36 then [chars[remaining%36]] else Digits(remaining/36)+[chars[remaining%36]]);
}

lemma SmallEncoding(n: int, chars: string)
  requires 0 <= n < 36
  requires chars == "0123456789abcdefghijklmnopqrstuvwxyz"
  ensures [chars[n]] == Digits(n)
{}

lemma EncodingComplete(original: int, output: string)
  requires EncodingProgress(original,0,output)
  ensures output == Digits(original)
{}

predicate ExactEncoding(n: int, output: string) { n >= 0 && output == Digits(n) }

lemma PowerPositive(k: int)
  requires k >= 0
  ensures PyPow(36,k) >= k+1
  ensures PyPow(36,k) > 0
  decreases k
{
  if k > 0 { PowerPositive(k-1); }
}

function Pad(n: int, k: int): string
  requires n >= 0 && k >= 0
  decreases k
{
  if k == 0 then "" else Pad(n/36,k-1)+["0123456789abcdefghijklmnopqrstuvwxyz"[n%36]]
}

lemma DividePower(n: int, p: int)
  requires n >= 0 && p > 0
  ensures n/(36*p) == (n/36)/p
  ensures (n%(36*p))/36 == (n/36)%p
  ensures (n%(36*p))%36 == n%36
{
  var q := (n/36)/p;
  var r := (n/36)%p;
  assert n == 36*p*q + 36*r + n%36;
  assert 0 <= 36*r+n%36 < 36*p;
  Quotient(n,36*p,q,36*r+n%36);
  assert n/(36*p) == q;
  assert n%(36*p) == 36*r+n%36;
  assert (36*r+n%36)/36 == r;
  assert (36*r+n%36)%36 == n%36;
}

lemma PadLeading(n: int, k: int)
  requires n >= 0 && k >= 0
  requires n < PyPow(36,k+1)
  ensures 0 <= n/PyPow(36,k) < 36
  ensures Pad(n,k+1) == ["0123456789abcdefghijklmnopqrstuvwxyz"[n/PyPow(36,k)]] + Pad(n%PyPow(36,k),k)
  decreases k
{
  PowerPositive(k);
  if k > 0 {
    PowerPositive(k-1);
    DividePower(n,PyPow(36,k-1));
    assert n/36 < PyPow(36,k);
    PadLeading(n/36,k-1);
  }
}

lemma DigitsPad(n: int, k: int)
  requires n >= 0 && k >= 0
  requires n < PyPow(36,k+1)
  requires k == 0 || PyPow(36,k) <= n
  ensures Digits(n) == Pad(n,k+1)
  decreases k
{
  PowerPositive(k);
  if k > 0 {
    PowerPositive(k-1);
    assert n >= 36;
    assert PyPow(36,k-1) <= n/36 < PyPow(36,k);
    DigitsPad(n/36,k-1);
  }
}

predicate LeadingProgress(original: int, remaining: int, factor: int, prefix: seq<string>)
{
  original >= 0 && remaining >= 0 && factor >= -1 &&
  remaining < PyPow(36,factor+1) &&
  Digits(original) == PyStrJoin("",prefix)+Pad(remaining,factor+1)
}

lemma StartEncoding(n: int, factor: int)
  requires n >= 0 && factor >= 0
  requires n < PyPow(36,factor+1)
  requires factor == 0 || PyPow(36,factor) <= n
  ensures LeadingProgress(n,n,factor,[])
{ DigitsPad(n,factor); }

lemma JoinAppend(prefix: seq<string>, s: string)
  ensures PyStrJoin("",prefix+[s]) == PyStrJoin("",prefix)+s
  decreases |prefix|
{
  if |prefix| > 0 {
    assert (prefix+[s])[1..] == prefix[1..]+[s];
    JoinAppend(prefix[1..],s);
  }
}

lemma LeadingStep(original: int, remaining: int, factor: int, prefix: seq<string>, chars: string)
  requires factor >= 0
  requires LeadingProgress(original,remaining,factor,prefix)
  requires chars == "0123456789abcdefghijklmnopqrstuvwxyz"
  ensures PyPow(36,factor) > 0
  ensures 0 <= remaining/PyPow(36,factor) < 36
  ensures LeadingProgress(original,remaining%PyPow(36,factor),factor-1,prefix+[[chars[remaining/PyPow(36,factor)]]])
{
  PowerPositive(factor);
  PadLeading(remaining,factor);
  JoinAppend(prefix,[chars[remaining/PyPow(36,factor)]]);
}

lemma Quotient(n: int, d: int, q: int, r: int)
  requires d > 0 && 0 <= r < d && n == d*q+r
  ensures n/d == q && n%d == r
{
  assert n == d*(n/d)+n%d;
  if n/d < q {
    assert n/d+1 <= q;
    assert d*(n/d+1) <= d*q;
    assert n < d*q;
  } else if n/d > q {
    assert q+1 <= n/d;
    assert d*(q+1) <= d*(n/d);
    assert n < d*(n/d);
  }
}

lemma PythonLeadingStep(original: int, remaining: int, factor: int, prefix: seq<string>, chars: string)
  requires factor >= 0
  requires LeadingProgress(original,remaining,factor,prefix)
  requires chars == "0123456789abcdefghijklmnopqrstuvwxyz"
  ensures PyPow(36,factor) > 0
  ensures 0 <= PyFloorDiv(remaining,PyPow(36,factor)) < |chars|
  ensures 0 <= PyIndex(PyFloorDiv(remaining,PyPow(36,factor)),|chars|) < |chars|
  ensures LeadingProgress(original,PyMod(remaining,PyPow(36,factor)),factor-1,prefix+[[chars[PyIndex(PyFloorDiv(remaining,PyPow(36,factor)),|chars|)]]])
{
  LeadingStep(original,remaining,factor,prefix,chars);
  PythonDivision(remaining,PyPow(36,factor));
  assert PyFloorDiv(remaining,PyPow(36,factor)) == remaining/PyPow(36,factor);
  assert PyMod(remaining,PyPow(36,factor)) == remaining%PyPow(36,factor);
}

lemma PythonDivision(n: int, d: int)
  requires n >= 0 && d > 0
  ensures PyFloorDiv(n,d) == n/d && PyMod(n,d) == n%d
{
  assert n == d*(n/d)+n%d;
  Quotient(n-n%d,d,n/d,0);
}
