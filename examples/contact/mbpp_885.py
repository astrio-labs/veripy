"""MBPP/885 — are two strings isomorphic (a bijective renaming of characters maps one onto the other)?"""


#@ verified
#@ ensures result == (len(str1) == len(str2) and (forall i in range(len(str1)), j in range(len(str1)) :: (str1[i] == str1[j]) == (str2[i] == str2[j])))
def is_Isomorphic(str1: str, str2: str) -> bool:
    dict_str1: dict[str, list[int]] = {}
    dict_str2: dict[str, list[int]] = {}
    for i, value in enumerate(str1):
        #@ invariant forall c in dict_str1, k in dict_str1[c] :: 0 <= k < i and str1[k] == c
        #@ invariant forall k in range(i) :: str1[k] in dict_str1 and k in dict_str1[str1[k]]
        dict_str1[value] = dict_str1.get(value, []) + [i]
    for j, value in enumerate(str2):
        #@ invariant forall c in dict_str2, k in dict_str2[c] :: 0 <= k < j and str2[k] == c
        #@ invariant forall k in range(j) :: str2[k] in dict_str2 and k in dict_str2[str2[k]]
        dict_str2[value] = dict_str2.get(value, []) + [j]
    if sorted(dict_str1.values()) == sorted(dict_str2.values()):
        return True
    else:
        return False
