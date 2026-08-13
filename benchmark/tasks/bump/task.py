"""Smallest possible old() demo."""


#@ verified
#@ ensures result == old(x) + 1
def bump(x: int) -> int:
    return x + 1
