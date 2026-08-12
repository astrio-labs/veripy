"""HumanEval/35 — return the maximum element in the list.

Canonical single-pass max kept; the for-each loop is rewritten over
indices so the loop invariant can name the processed prefix.
"""


#@ verified
#@ requires len(l) > 0
#@ ensures exists i in range(len(l)) :: result == l[i]
#@ ensures forall i in range(len(l)) :: l[i] <= result
def max_element(l: list[int]) -> int:
    m: int = l[0]
    for i in range(len(l)):
        #@ invariant 0 <= i < len(l)
        #@ invariant forall k in range(i) :: l[k] <= m
        #@ invariant exists k in range(len(l)) :: m == l[k]
        if l[i] > m:
            m = l[i]
    return m
