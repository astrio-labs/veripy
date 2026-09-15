#@ requires year >= 1
#@ ensures result == (year-1)*365 + (year-1)//4 - (year-1)//100 + (year-1)//400
def _days_before_year(year: int) -> int:
    """year -> number of days before January 1st of year."""
    y = year - 1
    return y * 365 + y // 4 - y // 100 + y // 400
