"""Clamp x into [lo, hi].

The postcondition DETERMINES the function: it says which of the three
outcomes occurs in which case, not merely that one of them does. The
weaker "result is one of x, lo, hi" form is satisfied by `return lo` — a
clamp that ignores its input — and the operand-replacement mutants
(`x` -> `lo`) exist precisely to refute that.
"""


#@ verified
#@ requires lo <= hi
#@ ensures lo <= result <= hi
#@ ensures x < lo ==> result == lo
#@ ensures x > hi ==> result == hi
#@ ensures lo <= x <= hi ==> result == x
def clamp(x: int, lo: int, hi: int) -> int:
    return min(max(x, lo), hi)
