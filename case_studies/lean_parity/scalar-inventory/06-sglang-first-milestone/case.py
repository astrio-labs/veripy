#@ requires y > 0
#@ ensures (result - 1) * y < x <= result * y
def ceil_div(x: int, y: int) -> int:
    #@ proof FloorDivFacts(x + y - 1, y)
    return (x + y - 1) // y

#@ requires y > 0
#@ ensures result % y == 0
#@ ensures x <= result < x + y
def ceil_align(x: int, y: int) -> int:
    #@ proof AlignedMultiples(y)
    return ceil_div(x, y) * y
