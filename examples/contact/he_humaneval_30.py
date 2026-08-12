"""HumanEval/30 — return only the positive numbers in the list."""


#@ verified
#@ ensures forall x in result :: x > 0
#@ ensures forall x in result :: x in l
#@ ensures forall x in l :: x > 0 ==> l.count(x) == result.count(x)
#@ ensures result == [x for x in l if x > 0]
def get_positive(l: list[int]) -> list[int]:
    return [e for e in l if e > 0]
