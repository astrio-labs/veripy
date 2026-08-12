"""HumanEval/34 — unique: sorted unique elements of a list."""


#@ verified
#@ ensures forall i in range(len(result) - 1) :: result[i] < result[i + 1]
#@ ensures forall i in range(len(result)) :: result[i] in l
#@ ensures forall i in range(len(l)) :: l[i] in result
def unique(l: list[int]) -> list[int]:
    return sorted(list(set(l)))
