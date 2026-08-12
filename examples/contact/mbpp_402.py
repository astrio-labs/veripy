"""MBPP/402 — C(n, r) mod p via Pascal's rule on a single DP row."""


def comb_spec(n: int, r: int) -> int:
    """Reference binomial coefficient: C(n, r), defined as 0 outside 0 <= r <= n."""
    if r < 0 or r > n:
        return 0
    num = 1
    den = 1
    for i in range(r):
        num *= n - i
        den *= i + 1
    return num // den


#@ verified
#@ requires n >= 0 and r >= 0 and p >= 2
#@ ensures result == comb_spec(n, r) % p
def ncr_modp(n: int, r: int, p: int) -> int:
    C: list[int] = [0 for _ in range(r + 1)]
    C[0] = 1
    for i in range(1, n + 1):
        #@ invariant forall t in range(r + 1) :: C[t] == comb_spec(i - 1, t) % p
        for j in range(min(i, r), 0, -1):
            #@ invariant forall t in range(j + 1, r + 1) :: C[t] == comb_spec(i, t) % p
            #@ invariant forall t in range(j + 1) :: C[t] == comb_spec(i - 1, t) % p
            C[j] = (C[j] + C[j - 1]) % p
    return C[r]
