"""MBPP-style — sum of squares of a list of integers.

Exercises the generator-expression fold: `sum(x * x for x in values)`
encodes to PySum over a mapped seq. The executable `assert` states the
mapped slice-extension fact (a list-comprehension equality — a runtime
check in CPython, a proof hint in Dafny).
"""


#@ verified
#@ ensures result == sum(x * x for x in values)
def sum_of_squares(values: list[int]) -> int:
    total = 0
    for i in range(len(values)):
        #@ invariant total == sum(x * x for x in values[:i])
        assert [x * x for x in values[:i + 1]] \
            == [x * x for x in values[:i]] + [values[i] * values[i]]
        total = total + values[i] * values[i]
    assert [x * x for x in values[:len(values)]] == [x * x for x in values]
    return total
