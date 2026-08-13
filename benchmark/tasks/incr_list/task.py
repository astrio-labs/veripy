"""HumanEval/42 — return the list with every element incremented by 1."""


#@ verified
#@ ensures len(result) == len(l)
#@ ensures forall i in range(len(l)) :: result[i] == l[i] + 1
def incr_list(l: list[int]) -> list[int]:
    return [(e + 1) for e in l]
