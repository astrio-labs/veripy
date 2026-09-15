function VPackagingCollapse(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if |s| >= 2 && s[..2] == "--" then VPackagingCollapse(s[1..])
  else s[..1] + VPackagingCollapse(s[1..])
}
predicate VPackagingInvariant(name: string, value: string) {
  VPackagingCollapse(value) == VPackagingCollapse(PyStrReplace(PyStrReplace(VUnicodeLower(name),"_","-"),".","-"))
}
predicate VPackagingOutcome(name: string, validate: bool, value: string, error: bool) {
  error == (validate && !VRegexValidName(name)) &&
  (!error ==> value == VPackagingCollapse(PyStrReplace(PyStrReplace(VUnicodeLower(name),"_","-"),".","-")))
}
predicate VPackagingNormalized(name: string, result: bool, error: bool) {
  !error && result == VRegexNormalizedName(name)
}
lemma VPackagingDash(s: string)
  ensures VPackagingCollapse("--"+s) == VPackagingCollapse("-"+s)
{}
lemma VPackagingReplace(s: string)
  ensures VPackagingCollapse(PyStrReplace(s,"--","-")) == VPackagingCollapse(s)
  ensures |PyStrReplace(s,"--","-")| <= |s|
  ensures PyStrFind(s,"--") >= 0 ==> |PyStrReplace(s,"--","-")| < |s|
  decreases |s|
{
  if |s| >= 2 {
    if s[..2] == "--" {
      VPackagingReplace(s[2..]);
      VPackagingPrefix(s[2..],PyStrReplace(s[2..],"--","-"),'-');
    } else {
      VPackagingReplace(s[1..]);
      VPackagingPrefix(s[1..],PyStrReplace(s[1..],"--","-"),s[0]);
    }
  }
}
lemma VPackagingHead(s: string)
  ensures (|VPackagingCollapse(s)| == 0) == (|s| == 0)
  ensures |s| > 0 ==> VPackagingCollapse(s)[0] == s[0]
  decreases |s|
{
  if |s| >= 2 && s[..2] == "--" { VPackagingHead(s[1..]); }
}
lemma VPackagingPrepend(s: string, c: char)
  ensures VPackagingCollapse([c]+s) == (if c == '-' && |VPackagingCollapse(s)| > 0 && VPackagingCollapse(s)[0] == '-' then VPackagingCollapse(s) else [c]+VPackagingCollapse(s))
{
  VPackagingHead(s);
  assert ([c]+s)[1..] == s;
  if |s| > 0 { assert ([c]+s)[..2] == [c,s[0]]; }
}
lemma VPackagingPrefix(a: string, b: string, c: char)
  requires VPackagingCollapse(a) == VPackagingCollapse(b)
  ensures VPackagingCollapse([c]+a) == VPackagingCollapse([c]+b)
{ VPackagingPrepend(a,c); VPackagingPrepend(b,c); }
lemma VPackagingFinished(s: string)
  requires PyStrFind(s,"--") < 0
  ensures VPackagingCollapse(s) == s
  decreases |s|
{
  if |s| > 0 { VPackagingFinished(s[1..]); }
}
