#@ ensures True
def _check_shard_metadata_pair_overlap(shard1: ShardMetadata, shard2: ShardMetadata) -> bool:
    """
    Checks if two shards overlap.
    """
    ndims = len(shard1.shard_offsets)
    for i in range(ndims):
        if shard1.shard_offsets[i] >= shard2.shard_offsets[i] + shard2.shard_sizes[i]:
            return False
        if shard2.shard_offsets[i] >= shard1.shard_offsets[i] + shard1.shard_sizes[i]:
            return False
    return True
