"""Executable CPython decimal syntax over code points, pinned to its runtime data.

The character tables are shared input data with the Dafny model, not prover
results. The scanner below is a structurally recursive Lean program.
"""
import sys
import unicodedata
from veripy.backends.dafny.decimal import tables


def version():
    return f"unicode{unicodedata.unidata_version}-digits{sys.get_int_max_str_digits()}"


def prelude():
    starts, spaces = tables()
    return f'''
-- CPython {version()}
namespace VeriPy
private def decimalStarts : List Nat := {starts}
private def integerSpaces : List Nat := {list(range(9,14))+[32]+spaces}
def decimalDigit (c : Nat) : Option Int :=
  match decimalStarts.find? (fun start => decide (start ≤ c ∧ c < start+10)) with
  | some start => some (Int.ofNat (c-start))
  | none => none

def decimalScan : List Nat → Bool → Int → Nat → Option (Int × Nat)
  | [], previous, value, count => if previous && decide (count > 0) then some (value,count) else none
  | c::cs, previous, value, count =>
      match decimalDigit c with
      | some digit => decimalScan cs true (value*10+digit) (count+1)
      | none => if c = 95 ∧ previous = true then decimalScan cs false value count else none

def tryDecimal (s : List Nat) : Option Int :=
  let trimmed := ((s.dropWhile (fun c => integerSpaces.contains c)).reverse.dropWhile (fun c => integerSpaces.contains c)).reverse
  let unsigned := if trimmed.headD 0 = 43 ∨ trimmed.headD 0 = 45 then trimmed.drop 1 else trimmed
  match decimalScan unsigned false 0 0 with
  | none => none
  | some (value,count) =>
      if {sys.get_int_max_str_digits()} = 0 ∨ count ≤ {sys.get_int_max_str_digits()} then
        some (if trimmed.headD 0 = 45 then -value else value)
      else none

def decimal (s : List Nat) : Except Error Int :=
  match tryDecimal s with
  | some value => pure value
  | none => raise Error.value
end VeriPy
'''
