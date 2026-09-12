from dataclasses import dataclass

@dataclass(frozen=True)
class _LinesMapping:
    original_start: int
    original_end: int
    modified_start: int
    modified_end: int
    is_changed_block: bool

#@ ensures result == (lines[0] <= lines[1])
def is_valid_line_range(lines: tuple[int, int]) -> bool:
    """Returns whether the line range is valid."""
    return not lines or lines[0] <= lines[1]

#@ requires 0 <= start_index <= len(lines_mappings)
#@ ensures start_index <= result <= len(lines_mappings)
#@ ensures result < len(lines_mappings) ==> lines_mappings[result].original_start <= original_line <= lines_mappings[result].original_end
#@ ensures forall k in range(start_index, result) :: not (lines_mappings[k].original_start <= original_line <= lines_mappings[k].original_end)
def _find_lines_mapping_index(
    original_line: int,
    lines_mappings: list[_LinesMapping],
    start_index: int,
) -> int:
    """Returns the original index of the lines mappings for the original line."""
    index = start_index
    while index < len(lines_mappings):
        #@ invariant start_index <= index <= len(lines_mappings)
        #@ invariant forall k in range(start_index, index) :: not (lines_mappings[k].original_start <= original_line <= lines_mappings[k].original_end)
        #@ decreases len(lines_mappings) - index
        mapping = lines_mappings[index]
        if mapping.original_start <= original_line <= mapping.original_end:
            return index
        index += 1
    return index

#@ ensures len(result) <= len(lines)
#@ ensures forall k in range(len(result)) :: result[k][0] <= result[k][1]
def adjusted_lines_from_mappings(lines: list[tuple[int, int]], lines_mappings: list[_LinesMapping]) -> list[tuple[int, int]]:
    new_lines: list[tuple[int, int]] = []
    # Keep an index of the current search. Since the lines and lines_mappings are
    # sorted, this makes the search complexity linear.
    current_mapping_index = 0
    #@ proof SortedPairs(lines)
    for start, end in sorted(lines):
        #@ invariant ghost("Progress", sorted(lines), lines_mappings, loop_index(), current_mapping_index, new_lines)
        #@ invariant 0 <= current_mapping_index <= len(lines_mappings)
        #@ invariant len(new_lines) <= loop_index()
        #@ invariant forall k in range(len(new_lines)) :: new_lines[k][0] <= new_lines[k][1]
        start_mapping_index = _find_lines_mapping_index(
            start,
            lines_mappings,
            current_mapping_index,
        )
        end_mapping_index = _find_lines_mapping_index(
            end,
            lines_mappings,
            start_mapping_index,
        )
        #@ proof PairEta(sorted(lines), loop_index(), start, end)
        #@ proof Advance(sorted(lines), lines_mappings, loop_index(), current_mapping_index, new_lines, start_mapping_index, end_mapping_index)
        current_mapping_index = start_mapping_index
        if start_mapping_index >= len(lines_mappings) or end_mapping_index >= len(
            lines_mappings
        ):
            # Protect against invalid inputs.
            #@ proof ExposeEmpty(lines_mappings, (start, end), start_mapping_index, end_mapping_index)
            #@ proof CheckNext(sorted(lines), lines_mappings, loop_index() + 1, current_mapping_index, new_lines)
            continue
        start_mapping = lines_mappings[start_mapping_index]
        end_mapping = lines_mappings[end_mapping_index]
        if start_mapping.is_changed_block:
            # When the line falls into a changed block, expands to the whole block.
            new_start: int = start_mapping.modified_start
        else:
            new_start = (
                start - start_mapping.original_start + start_mapping.modified_start
            )
        if end_mapping.is_changed_block:
            # When the line falls into a changed block, expands to the whole block.
            new_end: int = end_mapping.modified_end
        else:
            new_end = end - end_mapping.original_start + end_mapping.modified_start
        #@ proof ExposeEmit(lines_mappings, (start, end), start_mapping_index, end_mapping_index, new_start, new_end)
        new_range = (new_start, new_end)
        #@ proof CheckNext(sorted(lines), lines_mappings, loop_index() + 1, current_mapping_index, (new_lines + [new_range]) if new_range[0] <= new_range[1] else new_lines)
        if is_valid_line_range(new_range):
            new_lines.append(new_range)
    #@ proof Complete(lines, lines_mappings, current_mapping_index, new_lines)
    return new_lines
