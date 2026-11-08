"""Small executable components with source contracts and no verifier imports."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Interval:
    lower: int
    upper: int


# @ requires bounds.lower <= bounds.upper
# @ ensures result == (bounds.lower <= point <= bounds.upper)
def contains(bounds: Interval, point: int) -> bool:
    return bounds.lower <= point <= bounds.upper


# @ requires lower <= upper
# @ ensures len(result) == len(samples)
# @ ensures forall j in range(len(result)) :: result[j] == min(max(samples[j], lower), upper)
def clip_readings(samples: list[int], lower: int, upper: int) -> list[int]:
    return [min(max(sample, lower), upper) for sample in samples]


# @ requires count >= 0
# @ ensures result == start + count * stride
def advance(start: int, count: int, stride: int) -> int:
    value = start
    for _i in range(count):
        # @ invariant ghost("Progress", value, start, stride, _i)
        # @ proof ProgressStep(value, start, stride, _i)
        value += stride
    return value
