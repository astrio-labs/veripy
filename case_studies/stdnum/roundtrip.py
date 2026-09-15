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

#@ requires alphabet == "0123456789"
#@ requires all(c in alphabet for c in number)
#@ ensures len(result) == 1
#@ ensures all(c in alphabet for c in result)
#@ ghost_ensures ghost("LuhnCompleted", number, alphabet, result)
def calc_check_digit(number: str, alphabet: str = '0123456789') -> str:
    """Calculate the extra digit that should be appended to the number to
    make it a valid number."""
    ck = checksum(str(number) + alphabet[0], alphabet)
    #@ proof CheckDigitComplete(number, alphabet, ck)
    return alphabet[-ck]

#@ requires alphabet == "0123456789"
#@ requires all(c in alphabet for c in number)
#@ ensures result == 0
def check_digit_roundtrip(number: str, alphabet: str = '0123456789') -> int:
    digit = calc_check_digit(number, alphabet)
    return checksum(number + digit, alphabet)
