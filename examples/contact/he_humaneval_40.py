"""HumanEval/40 — is there a triple of distinct positions summing to zero?"""


#@ verified
#@ ensures result == (exists i in range(len(l)), j in range(i + 1, len(l)), k in range(j + 1, len(l)) :: l[i] + l[j] + l[k] == 0)
def triples_sum_to_zero(l: list[int]) -> bool:
    for i in range(len(l)):
        #@ invariant forall a in range(i), b in range(a + 1, len(l)), c in range(b + 1, len(l)) :: l[a] + l[b] + l[c] != 0
        for j in range(i + 1, len(l)):
            #@ invariant forall b in range(i + 1, j), c in range(b + 1, len(l)) :: l[i] + l[b] + l[c] != 0
            for k in range(j + 1, len(l)):
                #@ invariant forall c in range(j + 1, k) :: l[i] + l[j] + l[c] != 0
                if l[i] + l[j] + l[k] == 0:
                    return True
    return False
