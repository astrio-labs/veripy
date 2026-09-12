import math
import sys
from bisect import bisect_right, insort
from dataclasses import dataclass

@dataclass(frozen=True)
class ShardMetadata:
    shard_offsets: list[int]
    shard_sizes: list[int]

#@ requires len(shard1.shard_offsets) == len(shard1.shard_sizes) == len(shard2.shard_offsets) == len(shard2.shard_sizes)
#@ ensures result == (all(shard1.shard_offsets[j] < shard2.shard_offsets[j] + shard2.shard_sizes[j] and shard2.shard_offsets[j] < shard1.shard_offsets[j] + shard1.shard_sizes[j] for j in range(len(shard1.shard_offsets))))
def _check_shard_metadata_pair_overlap(shard1: ShardMetadata, shard2: ShardMetadata) -> bool:
    """
    Checks if two shards overlap.
    """

    # For each dim of each shard, check if one shard resides on the other
    # end of second shard with respect to that dim. As an example for a 2D
    # shard, we would check if one shard is above or on the left of the
    # other shard.
    ndims = len(shard1.shard_offsets)
    for i in range(ndims):
        #@ invariant forall j in range(i) :: shard1.shard_offsets[j] < shard2.shard_offsets[j] + shard2.shard_sizes[j] and shard2.shard_offsets[j] < shard1.shard_offsets[j] + shard1.shard_sizes[j]
        if shard1.shard_offsets[i] >= shard2.shard_offsets[i] + shard2.shard_sizes[i]:
            return False
        if shard2.shard_offsets[i] >= shard1.shard_offsets[i] + shard1.shard_sizes[i]:
            return False

    return True

#@ requires len(shards) <= sys.maxsize
#@ requires len(shards) <= 1 or len(sharded_dims) > 0
#@ requires forall a in range(len(shards)) :: len(shards[a].shard_offsets) == len(shards[a].shard_sizes) and len(shards[a].shard_offsets) == len(shards[0].shard_offsets)
#@ requires forall a in range(len(shards)), k in range(len(shards[a].shard_sizes)) :: shards[a].shard_sizes[k] > 0
#@ requires len(shards) == 0 or (forall k in range(len(sharded_dims)) :: 0 <= sharded_dims[k] < len(shards[0].shard_offsets))
#@ ensures result is not None ==> 0 <= result[0] < len(shards) and 0 <= result[1] < len(shards) and result[0] != result[1]
#@ ensures result is not None ==> not ((exists d in range(len(shards[result[0]].shard_offsets)) :: shards[result[0]].shard_offsets[d] + shards[result[0]].shard_sizes[d] <= shards[result[1]].shard_offsets[d] or shards[result[1]].shard_offsets[d] + shards[result[1]].shard_sizes[d] <= shards[result[0]].shard_offsets[d]))
#@ ensures result is None ==> not (exists a in range(len(shards)), b in range(len(shards)) :: a != b and (forall d in range(len(shards[a].shard_offsets)) :: shards[a].shard_offsets[d] < shards[b].shard_offsets[d] + shards[b].shard_sizes[d] and shards[b].shard_offsets[d] < shards[a].shard_offsets[d] + shards[a].shard_sizes[d]))
def _find_nd_overlapping_shards(
    shards: list[ShardMetadata], sharded_dims: list[int]
) -> tuple[int, int] | None:
    """Find overlapping shards using sweep-line algorithm."""
    if len(shards) <= 1:
        return None

    dims = len(sharded_dims)
    if dims == 0:
        return None

    sweep_dim_idx = 0
    if dims > 1:
        max_size = 0
        for i, dim in enumerate(sharded_dims):
            #@ invariant 0 <= sweep_dim_idx < len(sharded_dims)
            dim_size = shards[0].shard_offsets[dim] + shards[0].shard_sizes[dim]
            if dim_size > max_size:
                max_size = dim_size
                sweep_dim_idx = i
    #@ proof SelectedDimension(shards, sharded_dims, sweep_dim_idx)
    sweep_dim = sharded_dims[sweep_dim_idx]

    sorted_indices = sorted(
        range(len(shards)),
        key=lambda idx: (
            shards[idx].shard_offsets[sweep_dim],
            *(shards[idx].shard_offsets[d] for d in sharded_dims if d != sweep_dim),
        ),
    )
    active: list[tuple[int, int]] = []

    for idx in sorted_indices:
        #@ invariant ghost("SweepDomain", shards, sorted_indices, sweep_dim)
        #@ invariant ghost("ActiveState", shards, sorted_indices, loop_index(), sweep_dim, active)
        #@ invariant ghost("ProcessedDisjoint", shards, sorted_indices, loop_index())
        current = shards[idx]
        start = current.shard_offsets[sweep_dim]
        end = start + current.shard_sizes[sweep_dim]

        cutoff = bisect_right(active, (start, sys.maxsize))
        #@ proof ActiveSuffix(shards, sorted_indices, loop_index(), sweep_dim, active, cutoff)
        if cutoff:
            del active[:cutoff]

        for _, other_idx in active:
            #@ invariant ghost("Scanned", shards, idx, active, loop_index())
            other = shards[other_idx]

            #@ proof ScannedStep(shards, idx, active, loop_index())
            if _check_shard_metadata_pair_overlap(current, other):
                return (other_idx, idx)
        #@ proof SweepStep(shards, sorted_indices, loop_index(), sweep_dim, active)
        #@ proof ActiveInsert(shards, sorted_indices, loop_index(), sweep_dim, active)
        insort(active, (end, idx))
    #@ proof SearchOverlapWitness(shards, sharded_dims)
    #@ proof AllPairs(shards, sorted_indices, sweep_dim, (exists a in range(len(shards)), b in range(len(shards)) :: a != b and (forall d in range(len(shards[a].shard_offsets)) :: shards[a].shard_offsets[d] < shards[b].shard_offsets[d] + shards[b].shard_sizes[d] and shards[b].shard_offsets[d] < shards[a].shard_offsets[d] + shards[a].shard_sizes[d])))
    return None


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

#@ requires len(shards) <= sys.maxsize
#@ requires forall a in range(len(shards)) :: len(shards[a].shard_offsets) == len(shards[a].shard_sizes) and len(shards[a].shard_offsets) == len(shards[0].shard_offsets)
#@ requires forall a in range(len(shards)) :: (forall k in range(len(shards[a].shard_sizes)) :: shards[a].shard_sizes[k] > 0)
#@ ensures raised() == (exists a in range(len(shards)), b in range(a+1, len(shards)) :: forall d in range(len(shards[a].shard_offsets)) :: shards[a].shard_offsets[d] < shards[b].shard_offsets[d] + shards[b].shard_sizes[d] and shards[b].shard_offsets[d] < shards[a].shard_offsets[d] + shards[a].shard_sizes[d])
def validate_non_overlapping_shards_metadata(shards: list[ShardMetadata]) -> None:
    """
    Ensures none of the shards overlap with each other.

    Args:
        shards(List[ShardMetadata]): List of :class:`ShardMetadata` objects representing
            each shard.
    Raises:
        ``ValueError`` if there's overlap in any two shards.
    """
    if not shards or len(shards) == 1:
        return

    sharded_dims: list[int] = []
    for dim in range(len(shards[0].shard_offsets)):
        #@ invariant ghost("Partitioned", shards, sharded_dims, dim)
        #@ proof PartitionAdvance(shards, sharded_dims, dim)
        for i in range(1, len(shards)):
            #@ invariant ghost("Partitioned", shards, sharded_dims, dim)
            #@ invariant ghost("SamePrefix", shards, dim, i)
            #@ invariant ghost("SamePrefix", shards, dim, len(shards)) ==> ghost("Partitioned", shards, sharded_dims, dim + 1)
            #@ proof PartitionAdvance(shards, sharded_dims, dim)
            if (
                shards[i].shard_offsets[dim] != shards[0].shard_offsets[dim]
                or shards[i].shard_sizes[dim] != shards[0].shard_sizes[dim]
            ):
                sharded_dims.append(dim)
                break

    pair: tuple[int, int] | None = None
    if len(sharded_dims) == 0:
        # if shard is all zeros, we should consider as pass
        #@ proof PositiveVolume(shards[0].shard_sizes)
        all_zeros: bool = all(
            # strictly limited all offsets to be 0 to pass
            # could loosen it later on
            shard.shard_offsets == [0] * len(shards[0].shard_offsets)
            and math.prod(shard.shard_sizes) == 0  # one dimension is 0
            for shard in shards
        )
        if all_zeros:
            return
        # All shards are the same, all dims are not partitioned. Choose any 2.
        pair = (0, 1)
    elif len(sharded_dims) == 1:
        # Shards are partitioned over only one dimension. Overlap can be found
        # using a O(nlogn) overlapping interval algorithm.
        pair = _find_1d_overlapping_shards(shards, sharded_dims[0])
    else:
        # Shards are partitioned over more than one dimension.
        # Use sweep-line algorithm for O(n log n) complexity.
        pair = _find_nd_overlapping_shards(shards, sharded_dims)

    #@ proof NoReturnedOverlap(shards, sharded_dims, pair)
    if pair:
        #@ proof ReturnedOverlap(shards, sharded_dims, pair)
        raise ValueError(f"Shards {shards[pair[0]]} and {shards[pair[1]]} overlap")

