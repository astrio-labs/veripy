"""HumanEval/60 — sum_to_n(n) = 1 + 2 + ... + n.

The closed form is the interesting postcondition: proving the loop
computes `n * (n + 1) // 2` needs the Gauss step as a lemma, because
carrying the invariant across an iteration requires knowing that a product
of consecutive integers is even — which floor division hides from the SMT
solver. That lemma pack lives in the `.proofs.dfy` sidecar.
"""


#@ verified
#@ requires n >= 0
#@ ensures result == n * (n + 1) // 2
def sum_to_n(n: int) -> int:
    total = 0
    i = 1
    while i <= n:
        #@ invariant 1 <= i <= n + 1
        #@ invariant total == (i - 1) * i // 2
        #@ decreases n - i
        #@ proof GaussStep(i)
        total = total + i
        i = i + 1
    return total
