"""Binary search over a sorted list — the README example."""


#@ verified
#@ requires forall i in range(len(xs) - 1) :: xs[i] <= xs[i + 1]
#@ ensures result == -1 or (0 <= result < len(xs) and xs[result] == target)
def binary_search(xs: list[int], target: int) -> int:
    lo, hi = 0, len(xs)
    while lo < hi:
        #@ invariant 0 <= lo <= hi <= len(xs)
        #@ invariant forall k in range(lo) :: xs[k] < target
        #@ invariant forall k in range(hi, len(xs)) :: xs[k] > target
        mid = (lo + hi) // 2
        if xs[mid] < target:
            lo = mid + 1
        elif xs[mid] > target:
            hi = mid
        else:
            return mid
    return -1
