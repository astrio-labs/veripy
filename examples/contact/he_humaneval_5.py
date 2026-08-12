"""HumanEval/5 — insert `delimeter` between every two consecutive elements.

Canonical algorithm kept; the local accumulator is renamed from `result`
to `out` because `result` is a reserved spec word (v0 fragment rule).
"""


#@ verified
#@ ensures len(result) == (0 if len(numbers) == 0 else 2 * len(numbers) - 1)
#@ ensures forall i in range(len(result)) :: (i % 2 == 0 ==> result[i] == numbers[i // 2])
#@ ensures forall i in range(len(result)) :: (i % 2 == 1 ==> result[i] == delimeter)
def intersperse(numbers: list[int], delimeter: int) -> list[int]:
    if not numbers:
        return []

    out: list[int] = []

    for n in numbers[:-1]:
        #@ invariant len(out) % 2 == 0
        #@ invariant len(out) <= 2 * (len(numbers) - 1)
        #@ invariant forall i in range(len(out)) :: (i % 2 == 0 ==> out[i] == numbers[i // 2])
        #@ invariant forall i in range(len(out)) :: (i % 2 == 1 ==> out[i] == delimeter)
        out.append(n)
        out.append(delimeter)

    out.append(numbers[-1])

    return out
