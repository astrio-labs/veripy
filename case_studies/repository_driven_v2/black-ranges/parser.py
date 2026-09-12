#@ ensures raised() == (not all(len(line_ranges[j].split("-")) == 2 and decimal_valid(line_ranges[j].split("-")[0]) and decimal_valid(line_ranges[j].split("-")[1]) for j in range(len(line_ranges))))
#@ ensures not raised() ==> len(result) == len(line_ranges)
#@ ensures not raised() ==> (forall j in range(len(line_ranges)) :: result[j] == (int(line_ranges[j].split("-")[0]), int(line_ranges[j].split("-")[1])))
def parse_line_ranges(line_ranges: list[str]) -> list[tuple[int, int]]:
    lines: list[tuple[int, int]] = []
    for lines_str in line_ranges:
        #@ invariant len(lines) == loop_index()
        #@ invariant all(len(line_ranges[j].split("-")) == 2 and decimal_valid(line_ranges[j].split("-")[0]) and decimal_valid(line_ranges[j].split("-")[1]) for j in range(loop_index()))
        #@ invariant forall j in range(loop_index()) :: lines[j] == (int(line_ranges[j].split("-")[0]), int(line_ranges[j].split("-")[1]))
        parts = lines_str.split("-")
        if len(parts) != 2:
            raise ValueError(
                "Incorrect --line-ranges format, expect 'START-END', found"
                f" {lines_str!r}"
            )
        try:
            start = int(parts[0])
            end = int(parts[1])
        except ValueError:
            raise ValueError(
                "Incorrect --line-ranges value, expect integer ranges, found"
                f" {lines_str!r}"
            ) from None
        else:
            lines.append((start, end))
    return lines
