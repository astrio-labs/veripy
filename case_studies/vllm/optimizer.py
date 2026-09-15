#@ ensures raised() == (len(values) == 0 or (exists x in values :: x <= 0))
#@ ensures not raised() ==> result >= max(1, lower_bound if lower_bound is not None else 1)
#@ ensures not raised() and max(1, lower_bound if lower_bound is not None else 1) > max(values) ==> result == max(1, lower_bound if lower_bound is not None else 1)
#@ ensures not raised() and max(1, lower_bound if lower_bound is not None else 1) <= max(values) ==> result <= max(values)
#@ ensures not raised() ==> (forall c in range(max(1, lower_bound if lower_bound is not None else 1), max(values)+1) :: sum((result - (x % result)) % result for x in values) <= sum((c - (x % c)) % c for x in values))
#@ ensures not raised() ==> (forall c in range(max(1, lower_bound if lower_bound is not None else 1), max(values)+1) :: sum((result - (x % result)) % result for x in values) == sum((c - (x % c)) % c for x in values) ==> result >= c)
def _approximate_gcd(values: list[int], *, lower_bound: int | None = None) -> int:
    """Pick a chunk size that minimizes total upward padding.

    Each x is rounded up to a multiple of d:

      x -> ceil(x / d) * d

    Total padding is:

      pad(d) = sum_i (ceil(x_i / d) * d - x_i)

    We brute-force d in [lower_bound, max(values)] (fine for small lists / small
    maxima) and return the d with minimum padding. Ties prefer larger d.
    """
    if not values:
        raise ValueError("values must be non-empty")
    if any(x <= 0 for x in values):
        raise ValueError(f"values must be positive, got: {list(values)!r}")

    min_d = max(1, lower_bound if lower_bound is not None else 1)
    max_d = max(values)
    if min_d > max_d:
        return min_d

    best_d = min_d
    best_pad: int | None = None
    for d in range(min_d, max_d + 1):
        #@ invariant 1 <= min_d <= best_d <= max_d
        #@ invariant best_pad is None <==> d == min_d
        #@ invariant best_pad is not None ==> best_d < d
        #@ invariant best_pad is not None ==> best_pad == sum((best_d - (x % best_d)) % best_d for x in values)
        #@ invariant best_pad is not None ==> (forall c in range(min_d, d) :: best_pad <= sum((c - (x % c)) % c for x in values))
        #@ invariant best_pad is not None ==> (forall c in range(min_d, d) :: best_pad == sum((c - (x % c)) % c for x in values) ==> best_d >= c)
        pad = sum((d - (x % d)) % d for x in values)
        if best_pad is None or pad < best_pad or (pad == best_pad and d > best_d):
            best_pad = pad
            best_d = d

    return best_d

