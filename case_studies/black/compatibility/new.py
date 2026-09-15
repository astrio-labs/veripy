#@ ensures result == (lines[0] <= lines[1])
def is_valid_line_range(lines: tuple[int, int]) -> bool:
    """Returns whether the line range is valid."""
    return lines[0] <= lines[1]
