from dataclasses import dataclass

@dataclass(frozen=True)
class _LinesMapping:
    original_start: int
    original_end: int
    modified_start: int
    modified_end: int
    is_changed_block: bool

@dataclass(frozen=True)
class Match:
    a: int
    b: int
    size: int

#@ ensures len(result) <= 2 * len(matching_blocks)
def mappings_from_blocks(matching_blocks: list[Match]) -> list[_LinesMapping]:
    lines_mappings: list[_LinesMapping] = []
    # matching_blocks is a sequence of "same block of code ranges", see
    # https://docs.python.org/3/library/difflib.html#difflib.SequenceMatcher.get_matching_blocks
    # Each block corresponds to a _LinesMapping with is_changed_block=False,
    # and the ranges between two blocks corresponds to a _LinesMapping with
    # is_changed_block=True,
    # NOTE: matching_blocks is 0-based, but _LinesMapping is 1-based.
    for i, block in enumerate(matching_blocks):
        #@ invariant len(lines_mappings) <= 2 * i
        #@ invariant ghost("MappingProgress", matching_blocks, i, lines_mappings)
        #@ proof MappingStep(matching_blocks, i, lines_mappings)
        if i == 0:
            if block.a != 0 or block.b != 0:
                lines_mappings.append(
                    _LinesMapping(
                        original_start=1,
                        original_end=block.a,
                        modified_start=1,
                        modified_end=block.b,
                        is_changed_block=False,
                    )
                )
        else:
            previous_block = matching_blocks[i - 1]
            lines_mappings.append(
                _LinesMapping(
                    original_start=previous_block.a + previous_block.size + 1,
                    original_end=block.a,
                    modified_start=previous_block.b + previous_block.size + 1,
                    modified_end=block.b,
                    is_changed_block=True,
                )
            )
        if i < len(matching_blocks) - 1:
            lines_mappings.append(
                _LinesMapping(
                    original_start=block.a + 1,
                    original_end=block.a + block.size,
                    modified_start=block.b + 1,
                    modified_end=block.b + block.size,
                    is_changed_block=False,
                )
            )
    #@ proof MappingComplete(matching_blocks, lines_mappings)
    return lines_mappings
