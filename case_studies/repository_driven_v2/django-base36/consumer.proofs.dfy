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
