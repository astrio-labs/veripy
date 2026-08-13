"""HumanEval/9 — rolling maximum of a list of integers.

Adaptations: the canonical accumulator `result` is renamed (reserved spec
word); the value loop is indexed so the invariants can name the iteration
count (grammar-contact finding #3); and one executable `assert` supplies
the slice-extension fact the prover needs — a runtime check in CPython,
a proof hint in Dafny.
"""


#@ verified
#@ ensures len(result) == len(numbers)
#@ ensures forall i in range(len(numbers)) :: result[i] == max(numbers[:i + 1])
def rolling_max(numbers: list[int]) -> list[int]:
    running_max: int | None = None
    maxes: list[int] = []

    for i in range(len(numbers)):
        #@ invariant len(maxes) == i
        #@ invariant (running_max is None) <==> (len(maxes) == 0)
        #@ invariant running_max is None or running_max == max(numbers[:len(maxes)])
        #@ invariant forall k in range(len(maxes)) :: maxes[k] == max(numbers[:k + 1])
        n = numbers[i]
        if running_max is None:
            running_max = n
        else:
            running_max = max(running_max, n)

        assert numbers[:i + 1] == numbers[:i] + [numbers[i]]
        maxes.append(running_max)

    return maxes
