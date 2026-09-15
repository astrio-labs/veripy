from dataclasses import dataclass

@dataclass(frozen=True)
class ShardMetadata:
    shard_offsets: list[int]
    shard_sizes: list[int]

#@ requires forall j in range(len(shards)) :: 0 <= dim < len(shards[j].shard_offsets) and len(shards[j].shard_sizes) == len(shards[j].shard_offsets) and shards[j].shard_sizes[dim] > 0
#@ ensures result is not None ==> 0 <= result[0] < len(shards) and 0 <= result[1] < len(shards) and result[0] != result[1]
#@ ensures result is not None ==> shards[result[0]].shard_offsets[dim] < shards[result[1]].shard_offsets[dim] + shards[result[1]].shard_sizes[dim] and shards[result[1]].shard_offsets[dim] < shards[result[0]].shard_offsets[dim] + shards[result[0]].shard_sizes[dim]
#@ ensures result is None ==> (forall a in range(len(shards)), b in range(len(shards)) :: a == b or shards[a].shard_offsets[dim] + shards[a].shard_sizes[dim] <= shards[b].shard_offsets[dim] or shards[b].shard_offsets[dim] + shards[b].shard_sizes[dim] <= shards[a].shard_offsets[dim])
def _find_1d_overlapping_shards(
    shards: list[ShardMetadata], dim: int
) -> tuple[int, int] | None:
    # (begin, end, index_in_shards). Begin and end are inclusive.
    intervals = [
        (s.shard_offsets[dim], s.shard_offsets[dim] + s.shard_sizes[dim] - 1, i)
        for i, s in enumerate(shards)
    ]
    intervals.sort()
    #@ proof PermutedRows(intervals, [(shards[j].shard_offsets[dim], shards[j].shard_offsets[dim] + shards[j].shard_sizes[dim] - 1, j) for j in range(len(shards))])
    for i in range(len(shards) - 1):
        #@ invariant forall j in range(i) :: intervals[j][1] < intervals[j + 1][0]
        if intervals[i][1] >= intervals[i + 1][0]:
            return (intervals[i][2], intervals[i + 1][2])
    #@ proof NoAdjacentOverlap(intervals)
    #@ proof PermutedDisjoint(intervals, [(shards[j].shard_offsets[dim], shards[j].shard_offsets[dim] + shards[j].shard_sizes[dim] - 1, j) for j in range(len(shards))])
    #@ proof ShardDisjoint(shards, dim, [(shards[j].shard_offsets[dim], shards[j].shard_offsets[dim] + shards[j].shard_sizes[dim] - 1, j) for j in range(len(shards))])
    return None
