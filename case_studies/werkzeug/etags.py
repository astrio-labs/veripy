from __future__ import annotations
import re
from werkzeug import datastructures as ds
_etag_re = re.compile(r'([Ww]/)?(?:"(.*?)"|(.*?))(?:\s*,\s*|$)')

#@ ensures raised() == ('"' in etag)
#@ ensures raised() or result == (('W/' if weak else '') + '"' + etag + '"')
#@ ghost_ensures ghost("VHttpQuoteCorrect", etag, weak, result, raised())
def quote_etag(etag: str, weak: bool = False) -> str:
    """Quote an etag.

    :param etag: the etag to quote.
    :param weak: set to `True` to tag it "weak".
    """
    if '"' in etag:
        raise ValueError("invalid etag")
    etag = f'"{etag}"'
    if weak:
        etag = f"W/{etag}"
    return etag

#@ ghost_ensures ghost("VHttpUnquoteCorrect", etag, result)
def unquote_etag(
    etag: str | None,
) -> tuple[str, bool] | tuple[None, None]:
    """Unquote a single etag:

    >>> unquote_etag('W/"bar"')
    ('bar', True)
    >>> unquote_etag('"bar"')
    ('bar', False)

    :param etag: the etag identifier to unquote.
    :return: a ``(etag, weak)`` tuple.
    """
    if not etag:
        return None, None
    etag = etag.strip()
    weak = False
    if etag.startswith(("W/", "w/")):
        weak = True
        etag = etag[2:]
    if etag[:1] == etag[-1:] == '"':
        etag = etag[1:-1]
    return etag, weak

#@ requires value is None or "\n" not in value
#@ ghost_ensures ghost("VHttpParsedCorrect", value, result)
def parse_etags(value: str | None) -> ds.ETags:
    """Parse an etag header.

    :param value: the tag header to parse
    :return: an :class:`~werkzeug.datastructures.ETags` object.
    """
    if not value:
        return ds.ETags()
    strong: list[str | None] = []
    weak: list[str | None] = []
    end = len(value)
    pos = 0
    #@ proof VHttpSetEmpty()
    while pos < end:
        #@ invariant 0 <= pos <= end
        #@ invariant end == len(value)
        #@ invariant ghost("VHttpParseInvariant", value, pos, strong, weak)
        #@ decreases end - pos
        match = _etag_re.match(value, pos)
        if match is None:
            break
        is_weak, quoted, raw = match.groups()
        if raw == "*":
            return ds.ETags(star_tag=True)
        elif quoted:
            raw = quoted
        #@ proof VHttpSetStep(strong, weak, raw)
        if is_weak:
            weak.append(raw)
        else:
            strong.append(raw)
        pos = match.end()
    return ds.ETags(strong, weak)
