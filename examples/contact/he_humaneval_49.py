"""HumanEval 49: 2^n modulo p, computed by iterated doubling (no big powers)."""


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
        #@ invariant 0 <= i < n
        #@ invariant ret == (2 ** i) % p
        ret = (2 * ret) % p
        i = i + 1
    return ret
