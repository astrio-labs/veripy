"""HumanEval/31 — return True iff a given number is prime."""


#@ verified
#@ ensures result ==> n >= 2
#@ ensures result ==> forall k in range(2, n) :: n % k != 0
#@ ensures not result and n >= 2 ==> exists k in range(2, n) :: n % k == 0
def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for k in range(2, n - 1):
        #@ invariant 2 <= k <= n - 2
        #@ invariant forall j in range(2, k) :: n % j != 0
        if n % k == 0:
            return False
    return True
