#@ requires allow_buffer_alias("result", "scanline")
#@ requires filter_unit >= 1
#@ requires len(scanline) == len(previous) == len(buffer("result"))
#@ ensures forall k in range(min(filter_unit, len(buffer("result")))) :: buffer("result")[k] == old_buffer("result")[k]
#@ ensures forall k in range(filter_unit, len(buffer("result"))) :: buffer("result")[k] == (old_buffer("scanline")[k] + buffer("result")[k-filter_unit]) % 256
def undo_filter_sub(filter_unit: int, scanline: bytearray, previous: bytearray, result: bytearray) -> None:
    """Undo sub filter."""
    ai = 0
    for i in range(filter_unit, len(result)):
        #@ invariant forall k in range(i, len(buffer("scanline"))) :: buffer("scanline")[k] == old_buffer("scanline")[k]
        #@ invariant ai == i - filter_unit
        #@ invariant forall k in range(min(filter_unit, len(buffer("result")))) :: buffer("result")[k] == old_buffer("result")[k]
        #@ invariant forall k in range(filter_unit, i) :: buffer("result")[k] == (old_buffer("scanline")[k] + buffer("result")[k-filter_unit]) % 256
        x = scanline[i]
        a = result[ai]
        result[i] = x + a & 255
        ai += 1

#@ requires allow_buffer_alias("result", "scanline")
#@ requires filter_unit >= 1
#@ requires len(scanline) == len(previous) == len(buffer("result"))
#@ ensures forall k in range(len(buffer("result"))) :: buffer("result")[k] == (old_buffer("scanline")[k] + previous[k]) % 256
def undo_filter_up(filter_unit: int, scanline: bytearray, previous: bytearray, result: bytearray) -> None:
    """Undo up filter."""
    for i in range(len(result)):
        #@ invariant forall k in range(i, len(buffer("scanline"))) :: buffer("scanline")[k] == old_buffer("scanline")[k]
        #@ invariant forall k in range(i) :: buffer("result")[k] == (old_buffer("scanline")[k] + previous[k]) % 256
        x = scanline[i]
        b = previous[i]
        result[i] = x + b & 255

#@ requires allow_buffer_alias("result", "scanline")
#@ requires filter_unit >= 1
#@ requires len(scanline) == len(previous) == len(buffer("result"))
#@ ghost_ensures ghost("VFilterOutput", old_buffer("scanline"), buffer("previous"), buffer("result"), filter_unit, False)
def undo_filter_average(filter_unit: int, scanline: bytearray, previous: bytearray, result: bytearray) -> None:
    """Undo up filter."""
    ai = -filter_unit
    for i in range(len(result)):
        #@ invariant forall k in range(i, len(buffer("scanline"))) :: buffer("scanline")[k] == old_buffer("scanline")[k]
        #@ invariant ai == i - filter_unit
        #@ invariant ghost("VFilterPrefix", old_buffer("scanline"), buffer("previous"), buffer("result"), filter_unit, i, False)
        x = scanline[i]
        if ai < 0:
            a = 0
        else:
            a = result[ai]
        b = previous[i]
        #@ proof VFilterAdvance(old_buffer("scanline"), buffer("previous"), buffer("result"), filter_unit, i, False)
        result[i] = x + (a + b >> 1) & 255
        ai += 1

#@ requires allow_buffer_alias("result", "scanline")
#@ requires filter_unit >= 1
#@ requires len(scanline) == len(previous) == len(buffer("result"))
#@ ghost_ensures ghost("VFilterOutput", old_buffer("scanline"), buffer("previous"), buffer("result"), filter_unit, True)
def undo_filter_paeth(filter_unit: int, scanline: bytearray, previous: bytearray, result: bytearray) -> None:
    """Undo Paeth filter."""
    ai = -filter_unit
    for i in range(len(result)):
        #@ invariant forall k in range(i, len(buffer("scanline"))) :: buffer("scanline")[k] == old_buffer("scanline")[k]
        #@ invariant ai == i - filter_unit
        #@ invariant ghost("VFilterPrefix", old_buffer("scanline"), buffer("previous"), buffer("result"), filter_unit, i, True)
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
        #@ proof VFilterAdvance(old_buffer("scanline"), buffer("previous"), buffer("result"), filter_unit, i, True)
        result[i] = x + pr & 255
        ai += 1
