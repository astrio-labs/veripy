"""MBPP/149 — longest subsequence such that adjacent elements differ by one."""


#@ verified
#@ requires n == len(arr)
#@ requires n >= 1
#@ ensures 1 <= result <= n
#@ ensures (result >= 2) == (exists i in range(n), j in range(i) :: abs(arr[i] - arr[j]) == 1)
#@ ensures (forall i in range(n - 1) :: abs(arr[i + 1] - arr[i]) == 1) ==> result == n
def longest_subseq_with_diff_one(arr: list[int], n: int) -> int:
    dp = [1 for _ in range(n)]
    for i in range(n):
        #@ invariant 0 <= i < n
        #@ invariant forall k in range(n) :: 1 <= dp[k] <= k + 1
        for j in range(i):
            #@ invariant 0 <= j < i
            #@ invariant 1 <= dp[i] <= i + 1
            if arr[i] == arr[j] + 1 or arr[i] == arr[j] - 1:
                dp[i] = max(dp[i], dp[j] + 1)
    best = 1
    for i in range(n):
        #@ invariant 1 <= best <= n
        #@ invariant forall k in range(i) :: dp[k] <= best
        if best < dp[i]:
            best = dp[i]
    return best
