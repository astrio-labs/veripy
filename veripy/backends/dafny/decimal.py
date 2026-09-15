"""Unicode decimal-int model, pinned to the executing CPython Unicode database.

The generated artifact contains the complete Nd/whitespace tables and digit
limit; no uninterpreted conversion or trusted external procedure is used.
"""
from functools import lru_cache
import sys
import unicodedata


@lru_cache(maxsize=1)
def tables():
    starts = [i for i in range(0x110000) if unicodedata.decimal(chr(i), -1) == 0]
    assert all(unicodedata.decimal(chr(i+d), -1) == d for i in starts for d in range(10))
    spaces = [i for i in range(128, 0x110000) if chr(i).isspace()]
    return starts, spaces


def version():
    from veripy.backends.dafny.preamble import PREAMBLE_VERSION
    return f"{PREAMBLE_VERSION}-outcomes-1-unicode{unicodedata.unidata_version}-digits{sys.get_int_max_str_digits()}"


def preamble():
    starts, spaces = tables()
    digit = "\n  else ".join(f"if {i} <= c as int < {i+10} then c as int - {i}" for i in starts)
    white = " || ".join(f"c as int == {i}" for i in spaces)
    return f'''// {version()}; CPython decimal syntax, scalar Unicode strings.
function PyDecimalDigit(c: char): int {{
  {digit}
  else -1
}}
predicate PyIntSpace(c: char) {{
  9 <= c as int <= 13 || c == ' ' || {white}
}}
function PyIntLStrip(s: string): string
  decreases |s|
{{ if |s| > 0 && PyIntSpace(s[0]) then PyIntLStrip(s[1..]) else s }}
function PyIntRStrip(s: string): string
  decreases |s|
{{ if |s| > 0 && PyIntSpace(s[|s|-1]) then PyIntRStrip(s[..|s|-1]) else s }}
function PyIntTrim(s: string): string {{ PyIntRStrip(PyIntLStrip(s)) }}
function PyUnsignedDecimal(s: string): string {{
  if |s| > 0 && (s[0] == '+' || s[0] == '-') then s[1..] else s
}}
predicate PyDecimalBody(s: string) {{
  |s| > 0 && PyDecimalDigit(s[0]) >= 0 && PyDecimalDigit(s[|s|-1]) >= 0 &&
  (forall i :: 0 <= i < |s| ==>
    PyDecimalDigit(s[i]) >= 0 || (s[i] == '_' && 0 < i < |s|-1 &&
      PyDecimalDigit(s[i-1]) >= 0 && PyDecimalDigit(s[i+1]) >= 0))
}}
function PyDecimalCount(s: string): nat
  decreases |s|
{{ if |s| == 0 then 0 else PyDecimalCount(s[..|s|-1]) + (if PyDecimalDigit(s[|s|-1]) >= 0 then 1 else 0) }}
function PyDecimalValue(s: string): int
  decreases |s|
{{ if |s| == 0 then 0 else if s[|s|-1] == '_' then PyDecimalValue(s[..|s|-1])
   else PyDecimalValue(s[..|s|-1]) * 10 + PyDecimalDigit(s[|s|-1]) }}
opaque function PyTryDecimal(s: string): PyOpt<int>
  ensures |s| == 0 ==> PyTryDecimal(s).PyNone?
{{
  var t := PyIntTrim(s);
  var b := PyUnsignedDecimal(t);
  if PyDecimalBody(b) && ({sys.get_int_max_str_digits()} == 0 || PyDecimalCount(b) <= {sys.get_int_max_str_digits()})
  then PySome((if |t| > 0 && t[0] == '-' then -1 else 1) * PyDecimalValue(b))
  else PyNone
}}
'''
