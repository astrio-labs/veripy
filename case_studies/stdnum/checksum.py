#@ requires alphabet == "0123456789"
#@ requires all(c in alphabet for c in number)
#@ ensures 0 <= result < 10
#@ ghost_ensures ghost("LuhnExact", number, alphabet, result)
def checksum(number: str, alphabet: str = '0123456789') -> int:
    """Calculate the Luhn checksum over the provided number. The checksum
    is returned as an int. Valid numbers should have a checksum of 0."""
    n = len(alphabet)
    values = tuple(alphabet.index(i)
                   for i in reversed(str(number)))
    #@ proof LuhnBridge(number, alphabet, values, tuple(sum(divmod(i * 2, n)) for i in values[1::2]))
    return (sum(values[::2]) +
            sum(sum(divmod(i * 2, n))
                for i in values[1::2])) % n
