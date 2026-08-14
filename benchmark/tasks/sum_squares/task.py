"""MBPP-style — sum of squares of a list of integers.

Exercises the generator-expression fold: `sum(x * x for x in values)`
encodes to PySum over a mapped seq. The executable `assert`s state the
mapped slice-extension facts (list-comprehension equalities — runtime
checks in CPython, proof hints in Dafny). The nonnegativity postcondition
is inductive over PySum and needs the `SumNonNeg` lemma from the
`.proofs.dfy` sidecar, instantiated at the mapped seq via the `#@ proof`
clause's comprehension argument.
"""


#@ verified
#@ ensures result == sum(x * x for x in values)
#@ ensures result >= 0
def sum_of_squares(values: list[int]) -> int:
    total = 0
    for i in range(len(values)):
        #@ invariant total == sum(x * x for x in values[:i])
        assert [x * x for x in values[:i + 1]] \
            == [x * x for x in values[:i]] + [values[i] * values[i]]
        total = total + values[i] * values[i]
    assert [x * x for x in values[:len(values)]] == [x * x for x in values]
    #@ proof SumNonNeg([x * x for x in values])
    return total
