"""HumanEval/5 — insert `delimeter` between every two consecutive elements.

Adaptations: the local accumulator is renamed from `result` (reserved spec
word), and the canonical value-loop over `numbers[:-1]` is rewritten over
indices — the proof needs the invariant `len(out) == 2 * i`, and a value
loop has no nameable iteration state (grammar-contact finding #3).
"""


#@ verified
#@ ensures len(result) == (0 if len(numbers) == 0 else 2 * len(numbers) - 1)
#@ ensures forall i in range(len(result)) :: (i % 2 == 0 ==> result[i] == numbers[i // 2])
#@ ensures forall i in range(len(result)) :: (i % 2 == 1 ==> result[i] == delimeter)
def intersperse(numbers: list[int], delimeter: int) -> list[int]:
    if not numbers:
        return []

    out: list[int] = []

    for i in range(len(numbers) - 1):
        #@ invariant len(out) == 2 * i
        #@ invariant forall k in range(len(out)) :: (k % 2 == 0 ==> out[k] == numbers[k // 2])
        #@ invariant forall k in range(len(out)) :: (k % 2 == 1 ==> out[k] == delimeter)
        out.append(numbers[i])
        out.append(delimeter)

    out.append(numbers[-1])

    return out
