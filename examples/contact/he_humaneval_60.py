"""HumanEval/60 — sum_to_n(n) = 1 + 2 + ... + n.

The trailing `assert i == n + 1` states the loop's exit value — a
runtime check in CPython, a proof hint in both backends: Dafny lowers
it as a VC, and the Lean backend proves it from the invariant plus the
negated condition, then substitutes it into the spec proof so the
nonlinear atom (i-1)*i collapses to n*(n+1).

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
    assert i == n + 1
    return total
