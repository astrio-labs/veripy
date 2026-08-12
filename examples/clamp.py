"""Clamp x into [lo, hi] — contains a seeded bug for the CrossHair demo."""


#@ verified
#@ requires lo <= hi
#@ ensures lo <= result <= hi
#@ ensures result == x or result == lo or result == hi
def clamp(x: int, lo: int, hi: int) -> int:
    return min(x, hi)  # BUG: never applies the lower bound
