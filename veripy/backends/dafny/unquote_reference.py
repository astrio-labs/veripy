"""Pinned CPython urllib.parse dependency bodies, under the PSF license.

Used only for bytecode/provenance comparison, never as the formal model.
"""
import re
_hexdig = "0123456789ABCDEFabcdef"
_hextobyte = None
_asciire = re.compile("([\x00-\x7f]+)")

def _unquote_impl(string: bytes | bytearray | str) -> bytes | bytearray:
    # Note: strings are encoded as UTF-8. This is only an issue if it contains
    # unescaped non-ASCII characters, which URIs should not.
    if not string:
        # Is it a string-like object?
        string.split
        return b''
    if isinstance(string, str):
        string = string.encode('utf-8')
    bits = string.split(b'%')
    if len(bits) == 1:
        return string
    res = bytearray(bits[0])
    append = res.extend
    # Delay the initialization of the table to not waste memory
    # if the function is never called
    global _hextobyte
    if _hextobyte is None:
        _hextobyte = {(a + b).encode(): bytes.fromhex(a + b)
                      for a in _hexdig for b in _hexdig}
    for item in bits[1:]:
        try:
            append(_hextobyte[item[:2]])
            append(item[2:])
        except KeyError:
            append(b'%')
            append(item)
    return res

def _generate_unquoted_parts(string, encoding, errors):
    previous_match_end = 0
    for ascii_match in _asciire.finditer(string):
        start, end = ascii_match.span()
        yield string[previous_match_end:start]  # Non-ASCII
        # The ascii_match[1] group == string[start:end].
        yield _unquote_impl(ascii_match[1]).decode(encoding, errors)
        previous_match_end = end
    yield string[previous_match_end:]

def unquote(string, encoding='utf-8', errors='replace'):
    """Replace %xx escapes by their single-character equivalent. The optional
    encoding and errors parameters specify how to decode percent-encoded
    sequences into Unicode characters, as accepted by the bytes.decode()
    method.
    By default, percent-encoded sequences are decoded with UTF-8, and invalid
    sequences are replaced by a placeholder character.

    unquote('abc%20def') -> 'abc def'.
    """
    if isinstance(string, bytes):
        return _unquote_impl(string).decode(encoding, errors)
    if '%' not in string:
        # Is it a string-like object?
        string.split
        return string
    if encoding is None:
        encoding = 'utf-8'
    if errors is None:
        errors = 'replace'
    return ''.join(_generate_unquoted_parts(string, encoding, errors))
