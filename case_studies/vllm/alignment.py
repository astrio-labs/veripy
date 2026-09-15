#@ requires b != 0
#@ ensures b > 0 ==> (result - 1) * b < a <= result * b
#@ ensures b < 0 ==> (result - 1) * b > a >= result * b
def cdiv(a: int, b: int) -> int:
    """Ceiling division."""
    #@ proof FloorDivFacts(a, -b)
    return -(a // -b)

#@ requires y > 0
#@ ensures result % y == 0
#@ ensures x <= result < x + y
def round_up(x: int, y: int) -> int:
    """Round up x to the nearest multiple of y."""
    #@ proof FloorDivFacts(x + y - 1, y)
    return ((x + y - 1) // y) * y

#@ requires y > 0
#@ ensures result % y == 0
#@ ensures x - y < result <= x
def round_down(x: int, y: int) -> int:
    """Round down x to the nearest multiple of y."""
    #@ proof FloorDivFacts(x, y)
    return (x // y) * y
