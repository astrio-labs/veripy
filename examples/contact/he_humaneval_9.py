"""HumanEval/9 — rolling maximum of a list of integers.

The canonical solution names its accumulator ``result``; that identifier is a
reserved spec word (only meaningful in ``ensures``), so it is renamed ``maxes``.
"""


#@ verified
#@ ensures len(result) == len(numbers)
#@ ensures forall i in range(len(numbers)) :: result[i] == max(numbers[:i + 1])
def rolling_max(numbers: list[int]) -> list[int]:
    running_max: int | None = None
    maxes: list[int] = []

    for n in numbers:
        #@ invariant len(maxes) <= len(numbers)
        #@ invariant (running_max is None) == (len(maxes) == 0)
        #@ invariant running_max is None or running_max == max(numbers[:len(maxes)])
        #@ invariant forall i in range(len(maxes)) :: maxes[i] == max(numbers[:i + 1])
        if running_max is None:
            running_max = n
        else:
            running_max = max(running_max, n)

        maxes.append(running_max)

    return maxes
