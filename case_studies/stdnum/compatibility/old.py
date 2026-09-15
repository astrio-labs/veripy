from stdnum.exceptions import ValidationError, InvalidFormat, InvalidChecksum

#@ requires len(alphabet) > 1
#@ ensures raised() == (not all(alphabet.find(c) >= 0 for c in number))
#@ ensures raised() ==> raised("ValueError")
#@ ensures not raised() ==> 0 <= result < len(alphabet)
def checksum(number: str, alphabet: str = '0123456789') -> int:
    """Calculate the Luhn checksum over the provided number. The checksum
    is returned as an int. Valid numbers should have a checksum of 0."""
    n = len(alphabet)
    values = tuple(alphabet.index(i)
                   for i in reversed(str(number)))
    return (sum(values[::2]) +
            sum(sum(divmod(i * 2, n))
                for i in values[1::2])) % n

#@ requires len(alphabet) > 1
#@ ensures raised("InvalidFormat") == (len(number) == 0 or not all(alphabet.find(c) >= 0 for c in number))
#@ ensures raised() ==> raised("InvalidFormat") or raised("InvalidChecksum")
#@ ensures not raised() ==> result == number
def validate(number: str, alphabet: str = '0123456789') -> str:
    """Check if the number provided passes the Luhn checksum."""
    if not bool(number):
        raise InvalidFormat()
    try:
        valid = checksum(number, alphabet) == 0
    except Exception:  # noqa: B902
        raise InvalidFormat()
    if not valid:
        raise InvalidChecksum()
    return number

#@ requires len(alphabet) > 1
#@ ensures not raised()
#@ ensures result ==> len(number) > 0 and all(alphabet.find(c) >= 0 for c in number)
def is_valid(number: str, alphabet: str = '0123456789') -> bool:
    """Check if the number passes the Luhn checksum."""
    try:
        return bool(validate(number, alphabet))
    except ValidationError:
        return False

#@ requires len(alphabet) > 1
#@ ensures not raised() ==> len(result) == 1
def calc_check_digit(number: str, alphabet: str = '0123456789') -> str:
    """Calculate the extra digit that should be appended to the number to
    make it a valid number."""
    ck = checksum(str(number) + alphabet[0], alphabet)
    return alphabet[-ck]
