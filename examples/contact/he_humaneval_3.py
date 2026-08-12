"""HumanEval/3 — does the running balance of a transaction stream ever dip below zero?"""


#@ verified
#@ ensures result == (exists k in range(len(operations)) :: sum(operations[:k + 1]) < 0)
def below_zero(operations: list[int]) -> bool:
    balance = 0
    for i in range(len(operations)):
        #@ invariant balance == sum(operations[:i])
        #@ invariant forall k in range(i) :: sum(operations[:k + 1]) >= 0
        balance += operations[i]
        if balance < 0:
            return True
    return False
