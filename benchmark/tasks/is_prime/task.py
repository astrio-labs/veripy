"""HumanEval/31 — return True iff a given number is prime.

Adaptations: trial division is sqrt-bounded (`while k * k <= n`) and the
spec is the full iff — primality equals "no divisor in [2, n)". The gap
between the scanned range [2, k) and the promised range [2, n) is the
classic composite-has-a-small-factor argument: inductive divisibility
reasoning Z3 times out on unaided, supplied by the lemma pack in the
`.proofs.dfy` sidecar and invoked once at the True return.
"""


#@ verified
#@ ensures result == (n >= 2 and (forall d in range(2, n) :: n % d != 0))
def is_prime(n: int) -> bool:
    if n < 2:
        return False
    k = 2
    while k * k <= n:
        #@ invariant 2 <= k
        #@ invariant forall j in range(2, k) :: n % j != 0
        #@ decreases n - k
        if n % k == 0:
            return False
        k = k + 1
    #@ proof CompositeHasSmallFactor(n, k)
    return True
