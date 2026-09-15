#@ ensures raised() <==> old(i) < 0
#@ ensures not raised() ==> len(result) > 0
def int_to_base36(i: int) -> str:
    """Convert an integer to a base36 string."""
    char_set = "0123456789abcdefghijklmnopqrstuvwxyz"
    if i < 0:
        raise ValueError("Negative base36 conversion input.")
    if i < 36:
        #@ proof SmallEncoding(i, char_set)
        return char_set[i]
    b36 = ""
    while i != 0:
        #@ invariant i >= 0
        #@ invariant len(b36) > 0 or i >= 36
        #@ invariant ghost("EncodingProgress", old(i), i, b36)
        #@ decreases i
        #@ proof EncodingStep(old(i), i, b36, char_set)
        i, n = divmod(i, 36)
        b36 = char_set[n] + b36
    #@ proof EncodingComplete(old(i), b36)
    return b36
