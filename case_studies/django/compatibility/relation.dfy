lemma DigitsAgree(n: int)
  requires n >= 0
  ensures Old.Digits(n) == New.Digits(n)
  decreases n
{
  if n >= 36 { DigitsAgree(n/36); }
}

lemma CompatibilityRelation(i: int)
  ensures i >= 0 ==> Old.Digits(i) == New.Digits(i)
{
  if i >= 0 { DigitsAgree(i); }
}
