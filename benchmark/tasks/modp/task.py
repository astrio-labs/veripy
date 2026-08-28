"""HumanEval 49: 2^n modulo p, computed by iterated doubling (no big powers).

Adaptations for the proof backend: the loop invariant is exit-inclusive
(`i <= n` — Dafny checks invariants at the loop head including the final
test), and two `#@ proof` clauses invoke the sidecar's mod/pow lemmas —
ghost calls, so the no-big-powers property of the executable code holds.
"""


#@ verified
#@ requires n >= 0
#@ requires p >= 2
#@ ensures 0 <= result < p
#@ ensures result == (2 ** n) % p
def modp(n: int, p: int) -> int:
    # `for i in range(n)` in the canonical solution: the counter is needed by
    # the invariant, and a for-target read only by specs trips the strict
    # type gate (reportUnusedVariable), so the counter is explicit here.
    ret = 1
    i = 0
    while i < n:
        #@ invariant 0 <= i <= n
        #@ invariant ret == (2 ** i) % p
        #@ proof ModMulLeft(2 ** i, 2, p)
        #@ proof PowStepTwo(i)
        ret = (2 * ret) % p
        i = i + 1
    assert i == n
    return ret
