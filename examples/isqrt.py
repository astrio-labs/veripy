"""Integer square root by linear search, with the maximality spec.

`result * result <= n < (result + 1) * (result + 1)` follows from the loop
invariants alone. The clause worth having is maximality — no k in range
beats the answer — which is the same shape as gcd's, and notably Z3 DOES
close it here without proof additions: squaring's monotonicity on
non-negatives is within reach where divisibility was not. That contrast is
why the task is in the corpus without a sidecar.
"""


#@ verified
#@ requires n >= 0
#@ ensures result >= 0
#@ ensures result * result <= n
#@ ensures n < (result + 1) * (result + 1)
#@ ensures forall k in range(0, n + 1) :: k * k > n or k <= result
def isqrt(n: int) -> int:
    r = 0
    while (r + 1) * (r + 1) <= n:
        #@ invariant 0 <= r <= n
        #@ invariant r * r <= n
        #@ decreases n - r
        r = r + 1
    return r
