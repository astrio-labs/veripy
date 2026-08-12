"""HumanEval/13 — greatest common divisor of two integers, Euclid's algorithm."""


#@ verified
#@ requires a >= 0 and b >= 0
#@ requires a > 0 or b > 0
#@ ensures result >= 1
#@ ensures a % result == 0 and b % result == 0
#@ ensures forall d in range(result + 1, max(a, b) + 1) :: a % d != 0 or b % d != 0
def greatest_common_divisor(a: int, b: int) -> int:
    x, y = a, b
    while y != 0:
        #@ invariant x >= 0 and y >= 0
        #@ invariant x > 0 or y > 0
        #@ invariant forall d in range(1, max(a, b) + 1) :: (x % d == 0 and y % d == 0) == (a % d == 0 and b % d == 0)
        #@ decreases y
        x, y = y, x % y
    return x
