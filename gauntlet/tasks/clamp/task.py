"""Clamp x into [lo, hi]."""


#@ verified
#@ requires lo <= hi
#@ ensures lo <= result <= hi
#@ ensures result == x or result == lo or result == hi
def clamp(x: int, lo: int, hi: int) -> int:
    return min(max(x, lo), hi)
