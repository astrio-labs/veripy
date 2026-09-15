#@ ensures True
def _approximate_gcd(values: Sequence[int], *, lower_bound: int | None=None) -> int:
    """Pick a chunk size that minimizes total upward padding.

    Each x is rounded up to a multiple of d:

      x -> ceil(x / d) * d

    Total padding is:

      pad(d) = sum_i (ceil(x_i / d) * d - x_i)

    We brute-force d in [lower_bound, max(values)] (fine for small lists / small
    maxima) and return the d with minimum padding. Ties prefer larger d.
    """
    if not values:
        raise ValueError('values must be non-empty')
    if any((x <= 0 for x in values)):
        raise ValueError(f'values must be positive, got: {list(values)!r}')
    min_d = max(1, lower_bound if lower_bound is not None else 1)
    max_d = max(values)
    if min_d > max_d:
        return min_d
    best_d = min_d
    best_pad: int | None = None
    for d in range(min_d, max_d + 1):
        pad = sum(((d - x % d) % d for x in values))
        if best_pad is None or pad < best_pad or (pad == best_pad and d > best_d):
            best_pad = pad
            best_d = d
    return best_d
