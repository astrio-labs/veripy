_DAYS_IN_MONTH = [-1, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

_DAYS_BEFORE_MONTH = [-1]  # -1 is a placeholder for indexing purposes.
dbm = 0
for dim in _DAYS_IN_MONTH[1:]:
    _DAYS_BEFORE_MONTH.append(dbm)
    dbm += dim
del dbm, dim

#@ ensures result == (year % 4 == 0 and (year % 100 != 0 or year % 400 == 0))
def _is_leap(year: int) -> bool:
    """year -> 1 if leap year, else 0."""
    return year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)

#@ requires year >= 1
#@ ensures result == (year-1)*365 + (year-1)//4 - (year-1)//100 + (year-1)//400
#@ ensures result >= 0
def _days_before_year(year: int) -> int:
    """year -> number of days before January 1st of year."""
    y = year - 1
    return y * 365 + y // 4 - y // 100 + y // 400

#@ requires 1 <= month <= 12
#@ ensures result == (29 if month == 2 and (year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)) else _DAYS_IN_MONTH[month])
def _days_in_month(year: int, month: int) -> int:
    """year, month -> number of days in that month in that year."""
    assert 1 <= month <= 12, month
    if month == 2 and _is_leap(year):
        return 29
    return _DAYS_IN_MONTH[month]

#@ requires 1 <= month <= 12
#@ ensures result == _DAYS_BEFORE_MONTH[month] + (1 if month > 2 and (year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)) else 0)
def _days_before_month(year: int, month: int) -> int:
    """year, month -> number of days in year preceding first day of month."""
    assert 1 <= month <= 12, f'month must be in 1..12, not {month}'
    return _DAYS_BEFORE_MONTH[month] + (month > 2 and _is_leap(year))

#@ requires year >= 1
#@ requires 1 <= month <= 12
#@ requires 1 <= day <= (29 if month == 2 and (year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)) else _DAYS_IN_MONTH[month])
#@ ensures result >= 1
#@ ghost_ensures ghost("VCalendarEncoded", year, month, day, result)
def _ymd2ord(year: int, month: int, day: int) -> int:
    """year, month, day -> ordinal, considering 01-Jan-0001 as day 1."""
    assert 1 <= month <= 12, f'month must be in 1..12, not {month}'
    dim = _days_in_month(year, month)
    assert 1 <= day <= dim, f'day must be in 1..{dim}, not {day}'
    return _days_before_year(year) + _days_before_month(year, month) + day

_DI400Y = _days_before_year(401)    # number of days in 400 years
_DI100Y = _days_before_year(101)    #    "    "   "   " 100   "
_DI4Y   = _days_before_year(5)      #    "    "   "   "   4   "

# A 4-year cycle has an extra leap day over what we'd get from pasting
# together 4 single years.
assert _DI4Y == 4 * 365 + 1

# Similarly, a 400-year cycle has an extra leap day over what we'd get from
# pasting together 4 100-year cycles.
assert _DI400Y == 4 * _DI100Y + 1

# OTOH, a 100-year cycle has one fewer leap day than we'd get from
# pasting together 25 4-year cycles.
assert _DI100Y == 25 * _DI4Y - 1

#@ requires n >= 1
#@ ghost_ensures ghost("VCalendarDecoded", n, result)
def _ord2ymd(n: int) -> tuple[int, int, int]:
    """ordinal -> (year, month, day), considering 01-Jan-0001 as day 1."""
    n -= 1
    n400, n = divmod(n, _DI400Y)
    year = n400 * 400 + 1
    n100, n = divmod(n, _DI100Y)
    n4, n = divmod(n, _DI4Y)
    n1, n = divmod(n, 365)
    year += n100 * 100 + n4 * 4 + n1
    #@ proof VCalendarCycles(n400, n100, n4, n1, n)
    if n1 == 4 or n100 == 4:
        assert n == 0
        return (year - 1, 12, 31)
    leapyear = n1 == 3 and (n4 != 24 or n100 == 3)
    assert leapyear == _is_leap(year)
    month = n + 50 >> 5
    preceding = _DAYS_BEFORE_MONTH[month] + (month > 2 and leapyear)
    if preceding > n:
        month -= 1
        preceding -= _DAYS_IN_MONTH[month] + (month == 2 and leapyear)
    n -= preceding
    assert 0 <= n < _days_in_month(year, month)
    return (year, month, n + 1)

#@ requires n >= 1
#@ ensures result == n
def ordinal_round_trip(n: int) -> int:
    date = _ord2ymd(n)
    return _ymd2ord(date[0], date[1], date[2])

#@ requires year >= 1
#@ requires 1 <= month <= 12
#@ requires 1 <= day <= (29 if month == 2 and year % 4 == 0 and (year % 100 != 0 or year % 400 == 0) else _DAYS_IN_MONTH[month])
#@ ensures result == (year, month, day)
def date_round_trip(year: int, month: int, day: int) -> tuple[int, int, int]:
    ordinal = _ymd2ord(year, month, day)
    date = _ord2ymd(ordinal)
    #@ proof VCalendarUnique(year, month, day, date[0], date[1], date[2])
    return date
