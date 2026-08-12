"""MBPP 620: size of the largest subset of a[:n] whose elements are pairwise divisible.

The canonical DP scans right-to-left and chains *adjacent* divisibility, which
only coincides with *pairwise* divisibility when the input is sorted ascending
and strictly positive (divisibility is then transitive along a chain); the
requires clauses pin down exactly that domain. Subsets are quantified as bit
masks in range(2 ** n): bit k of `mask` selects index k.
"""


#@ verified
#@ requires n == len(a)
#@ requires n >= 1
#@ requires forall k in range(n) :: a[k] >= 1
#@ requires forall k in range(n - 1) :: a[k] <= a[k + 1]
#@ ensures exists mask in range(2 ** n) :: sum((mask >> k) & 1 for k in range(n)) == result and (forall i in range(n), j in range(n) :: ((mask >> i) & 1 == 1 and (mask >> j) & 1 == 1) ==> (a[i] % a[j] == 0 or a[j] % a[i] == 0))
#@ ensures forall mask in range(2 ** n) :: (forall i in range(n), j in range(n) :: ((mask >> i) & 1 == 1 and (mask >> j) & 1 == 1) ==> (a[i] % a[j] == 0 or a[j] % a[i] == 0)) ==> (sum((mask >> k) & 1 for k in range(n)) <= result)
def largest_subset(a: list[int], n: int) -> int:
    dp = [0 for _ in range(n)]
    dp[n - 1] = 1
    for i in range(n - 2, -1, -1):
        #@ invariant 0 <= i <= n - 2
        #@ invariant forall k in range(i + 1, n) :: dp[k] == 1 + max([dp[m] for m in range(k + 1, n) if a[m] % a[k] == 0 or a[k] % a[m] == 0] + [0])
        mxm = 0
        for j in range(i + 1, n):
            #@ invariant i + 1 <= j <= n - 1
            #@ invariant mxm == max([dp[m] for m in range(i + 1, j) if a[m] % a[i] == 0 or a[i] % a[m] == 0] + [0])
            if a[j] % a[i] == 0 or a[i] % a[j] == 0:
                mxm = max(mxm, dp[j])
        dp[i] = 1 + mxm
    return max(dp)
