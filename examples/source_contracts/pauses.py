"""A separate two-level pause policy over native immutable timedelta fields."""

from dataclasses import dataclass
from datetime import timedelta


@dataclass(frozen=True, slots=True)
class RetryWindow:
    base: timedelta
    cap: timedelta

    # @ requires self.base > timedelta(0) and self.cap >= self.base
    # @ ensures raised() == (attempt < 0)
    # @ ensures not raised() ==> result == (self.base if attempt == 0 else min(self.base * 2, self.cap))
    def pause(self, attempt: int) -> timedelta:
        if attempt < 0:
            raise ValueError("attempt must be nonnegative")
        if attempt == 0:
            return self.base
        if self.cap // self.base < 2:
            return self.cap
        return self.base * 2
