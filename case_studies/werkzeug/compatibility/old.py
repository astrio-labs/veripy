#@ ensures raised() == ('"' in etag)
#@ ensures raised() or result == (('W/' if weak else '') + '"' + etag + '"')
#@ ghost_ensures ghost("QuoteCorrect", etag, weak, result, raised())
def quote_etag(etag: str, weak: bool=False) -> str:
    """Quote an etag.

    :param etag: the etag to quote.
    :param weak: set to `True` to tag it "weak".
    """
    if '"' in etag:
        raise ValueError('invalid etag')
    etag = f'"{etag}"'
    if weak:
        etag = f'W/{etag}'
    return etag
