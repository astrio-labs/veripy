#@ ensures raised() <==> old(i) < 0
#@ ghost_ensures not raised() ==> ghost("ExactEncoding", old(i), result)
def int_to_base36(i: int) -> str:
    """
    Converts an integer to a base36 string
    """
    digits = '0123456789abcdefghijklmnopqrstuvwxyz'
    factor = 0
    if i < 0:
        raise ValueError('Negative base36 conversion input.')
    while True:
        #@ invariant i >= 0 and 0 <= factor <= i + 1
        #@ invariant factor == 0 or 36 ** factor <= i
        #@ decreases i + 1 - factor
        #@ proof PowerPositive(factor + 1)
        factor += 1
        if i < 36 ** factor:
            factor -= 1
            break
    #@ proof StartEncoding(i, factor)
    base36: list[str] = []
    while factor >= 0:
        #@ invariant factor >= -1 and i >= 0
        #@ invariant ghost("LeadingProgress", old(i), i, factor, base36)
        #@ decreases factor + 1
        #@ proof PythonLeadingStep(old(i), i, factor, base36, digits)
        j = 36 ** factor
        base36.append(digits[i // j])
        i = i % j
        factor -= 1
    return ''.join(base36)
