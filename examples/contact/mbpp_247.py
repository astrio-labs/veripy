"""MBPP/247 — length of the longest palindromic subsequence of a string."""


#@ verified
#@ requires len(s) >= 1
#@ ensures 1 <= result <= len(s)
#@ ensures (result == len(s)) == (forall i in range(len(s)) :: s[i] == s[len(s) - 1 - i])
#@ ensures (result >= 2) == (exists i in range(len(s)), j in range(i) :: s[i] == s[j])
def lps(s: str) -> int:
    n = len(s)
    table = [[0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        #@ invariant 0 <= i < n
        #@ invariant forall k in range(i) :: table[k][k] == 1
        table[i][i] = 1
    for cl in range(2, n + 1):
        #@ invariant 2 <= cl <= n
        #@ invariant forall a in range(n), b in range(n) :: 0 <= table[a][b] <= n
        for i in range(n - cl + 1):
            #@ invariant 0 <= i <= n - cl
            j = i + cl - 1
            if s[i] == s[j] and cl == 2:
                table[i][j] = 2
            elif s[i] == s[j]:
                table[i][j] = table[i + 1][j - 1] + 2
            else:
                table[i][j] = max(table[i][j - 1], table[i + 1][j])
    return table[0][n - 1]
