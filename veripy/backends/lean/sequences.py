"""Checked immutable sequence operations, included only when used."""
PRELUDE = r'''
def VeriPy.stringFind (s needle : List Nat) : Int :=
  if needle.isPrefixOf s then 0 else
  match s with
  | [] => -1
  | _::tail => let i := VeriPy.stringFind tail needle
               if i < 0 then -1 else i + 1

def VeriPy.stringIndex (s needle : List Nat) : Except VeriPy.Error Int :=
  let i := VeriPy.stringFind s needle
  if i < 0 then VeriPy.raise VeriPy.Error.value else pure i

def VeriPy.takeEveryAux : List α → Nat → Nat → List α
  | [], _, _ => []
  | x::tail, step, 0 => x :: VeriPy.takeEveryAux tail step (step-1)
  | _::tail, step, skip+1 => VeriPy.takeEveryAux tail step skip

def VeriPy.takeEvery (xs : List α) (step : Nat) : List α :=
  VeriPy.takeEveryAux xs step 0

def VeriPy.stride (xs : List α) (lo hi : Int) (step : Nat) : List α :=
  VeriPy.takeEvery (VeriPy.slice xs lo hi) step
'''
