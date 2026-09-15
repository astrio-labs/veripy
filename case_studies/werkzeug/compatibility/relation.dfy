lemma CompatibilityRelation(etag: string, weak: bool)
  ensures Old.PyStrFind(etag,"\"") == New.PyStrFind(etag,"\"")
  decreases |etag|
{
  if |etag| > 0 { CompatibilityRelation(etag[1..],weak); }
}
