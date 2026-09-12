#@ ensures result == ([] if len(src_contents) == 0 else [(max(lines[j][0], 1), min(lines[j][1], (src_contents.count("\n") + (0 if src_contents.endswith("\n") else 1)))) for j in range(len(lines)) if lines[j][0] <= (src_contents.count("\n") + (0 if src_contents.endswith("\n") else 1)) and lines[j][1] >= max(lines[j][0], 1)])
def sanitized_lines(
    lines: list[tuple[int, int]], src_contents: str
) -> list[tuple[int, int]]:
    """Returns the valid line ranges for the given source.

    This removes ranges that are entirely outside the valid lines.

    Other ranges are normalized so that the start values are at least 1 and the
    end values are at most the (1-based) index of the last source line.
    """
    if not src_contents:
        return []
    good_lines: list[tuple[int, int]] = []
    src_line_count = src_contents.count("\n")
    if not src_contents.endswith("\n"):
        src_line_count += 1
    for start, end in lines:
        #@ invariant good_lines == [(max(lines[j][0], 1), min(lines[j][1], src_line_count)) for j in range(loop_index()) if lines[j][0] <= src_line_count and lines[j][1] >= max(lines[j][0], 1)]
        #@ proof FlattenStep([([(max(lines[j][0], 1), min(lines[j][1], src_line_count))] if lines[j][0] <= src_line_count and lines[j][1] >= max(lines[j][0], 1) else []) for j in range(loop_index())], [([(max(lines[j][0], 1), min(lines[j][1], src_line_count))] if lines[j][0] <= src_line_count and lines[j][1] >= max(lines[j][0], 1) else []) for j in range(loop_index() + 1)])
        if start > src_line_count:
            continue
        # line-ranges are 1-based
        start = max(start, 1)
        if end < start:
            continue
        end = min(end, src_line_count)
        good_lines.append((start, end))
    return good_lines
