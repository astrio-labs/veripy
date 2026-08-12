"""HumanEval 43: do two distinct elements of the list sum to zero?"""


#@ verified
#@ ensures result == (exists i in range(len(l)), j in range(i + 1, len(l)) :: l[i] + l[j] == 0)
def pairs_sum_to_zero(l: list[int]) -> bool:
    for i, l1 in enumerate(l):
        #@ invariant 0 <= i < len(l)
        #@ invariant forall a in range(i), b in range(a + 1, len(l)) :: l[a] + l[b] != 0
        for j in range(i + 1, len(l)):
            #@ invariant i + 1 <= j < len(l)
            #@ invariant forall b in range(i + 1, j) :: l[i] + l[b] != 0
            if l1 + l[j] == 0:
                return True
    return False
