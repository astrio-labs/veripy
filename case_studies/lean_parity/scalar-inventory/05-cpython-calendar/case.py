__all__ = ['_is_leap', '_days_before_year']

#@ requires 1 <= year <= 9999
#@ ensures year % 400 == 0 ==> result
#@ ensures year % 100 == 0 and year % 400 != 0 ==> not result
#@ ensures year % 100 != 0 ==> result == (year % 4 == 0)
def _is_leap(year: int) -> bool:
    "year -> 1 if leap year, else 0."
    return year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)

#@ requires 1 <= year <= 9999
#@ ensures result == 365 * (year - 1) + (year - 1) // 4 - (year - 1) // 100 + (year - 1) // 400
#@ ensures 365 * (year - 1) <= result <= 366 * (year - 1)
#@ ensures result + (366 if year % 4 == 0 and (year % 100 != 0 or year % 400 == 0) else 365) == 365 * year + year // 4 - year // 100 + year // 400
def _days_before_year(year: int) -> int:
    "year -> number of days before January 1st of year."
    y = year - 1
    return y*365 + y//4 - y//100 + y//400
