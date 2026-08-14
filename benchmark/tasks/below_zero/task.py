"""HumanEval/3 — does the running balance of a transaction stream ever dip below zero?

Adaptations for the proof backend: the slice-extension fact that steps the
running `sum(...)` invariants is supplied by the `SliceSnoc` lemma (in the
`.proofs.dfy` sidecar beside this file), invoked per iteration via the
`#@ proof` clause; and the quantified prefix is written `operations[:n]`
(n one past the end) rather than `operations[:k + 1]`: arithmetic on the
bound variable inside the quantified term leaves the SMT solver no usable
trigger, and the original form times out.
"""


#@ verified
#@ ensures result == (exists n in range(len(operations) + 1) :: sum(operations[:n]) < 0)
def below_zero(operations: list[int]) -> bool:
    balance = 0
    for i in range(len(operations)):
        #@ invariant balance == sum(operations[:i])
        #@ invariant forall n in range(i + 1) :: sum(operations[:n]) >= 0
        #@ proof SliceSnoc(operations, i)
        balance += operations[i]
        if balance < 0:
            return True
    return False
