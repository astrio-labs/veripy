"""HumanEval/3 — does a running balance ever drop below zero?

Adaptations: the value loop is indexed so the invariants can name the
iteration count (grammar-contact finding #3), and one executable `assert`
supplies the slice-extension fact the prover needs to step the running
`sum(...)` invariant — a runtime check in CPython, a proof hint in Dafny.
"""


#@ verified
#@ ensures result <==> exists n in range(len(operations) + 1) :: sum(operations[:n]) < 0
def below_zero(operations: list[int]) -> bool:
    balance = 0
    found = False
    for i in range(len(operations)):
        #@ invariant balance == sum(operations[:i])
        #@ invariant found <==> exists n in range(i + 1) :: sum(operations[:n]) < 0
        assert operations[:i + 1] == operations[:i] + [operations[i]]
        balance = balance + operations[i]
        if balance < 0:
            found = True
    return found
