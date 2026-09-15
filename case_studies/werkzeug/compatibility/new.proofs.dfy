predicate QuoteCorrect(s: string, weak: bool, result: string, error: bool) {
  error == (PyStrFind(s,"\"") >= 0) && (!error ==> result == (if weak then "W/" else "") + "\"" + s + "\"")
}
