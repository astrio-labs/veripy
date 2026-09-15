#@ ensures True
def undo_filter_paeth(filter_unit: int, scanline: bytearray, previous: bytearray, result: bytearray) -> None:
    """Undo Paeth filter."""
    ai = -filter_unit
    for i in range(len(result)):
        x = scanline[i]
        if ai < 0:
            a = c = 0
        else:
            a = result[ai]
            c = previous[ai]
        b = previous[i]
        p = a + b - c
        pa = abs(p - a)
        pb = abs(p - b)
        pc = abs(p - c)
        if pa <= pb and pa <= pc:
            pr = a
        elif pb <= pc:
            pr = b
        else:
            pr = c
        result[i] = x + pr & 255
        ai += 1
