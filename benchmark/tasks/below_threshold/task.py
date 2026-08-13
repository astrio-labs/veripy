"""HumanEval/52 — below_threshold: is every number in the list below t?"""


#@ verified
#@ ensures result == (forall i in range(len(l)) :: l[i] < t)
def below_threshold(l: list[int], t: int) -> bool:
    for i in range(len(l)):
        #@ invariant forall k in range(i) :: l[k] < t
        if l[i] >= t:
            return False
    return True
