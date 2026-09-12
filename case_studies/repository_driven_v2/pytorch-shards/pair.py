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
