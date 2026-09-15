from dataclasses import dataclass
from math import prod

@dataclass(frozen=True)
class ShardMetadata:
    shard_offsets: list[int]
    shard_sizes: list[int]

#@ requires len(shards_metadata) > 0
#@ requires forall j in range(len(shards_metadata)) :: len(shards_metadata[j].shard_offsets) == len(shards_metadata[0].shard_offsets) and len(shards_metadata[j].shard_sizes) == len(shards_metadata[0].shard_offsets)
#@ ensures raised() == (len(tensor_dims) != len(shards_metadata[0].shard_offsets) or (not all(all(shards_metadata[j].shard_offsets[k] + shards_metadata[j].shard_sizes[k] <= tensor_dims[k] for k in range(len(tensor_dims))) for j in range(len(shards_metadata)))) or sum(prod(shards_metadata[j].shard_sizes) for j in range(len(shards_metadata))) != prod(tensor_dims))
def check_tensor(shards_metadata: list[ShardMetadata], tensor_dims: list[int]) -> None:
    """
    Checks if the shards_metadata is compatible with the provided tensor dims.

    Args:
        shards_metadata(List[ShardMetadata]): List of :class:`ShardMetadata`
            objects representing each shard of the tensor.
        tensor_dims(Sequence of int): Dimensions of tensor to verify
    Raises:
        ``ValueError`` if not compatible.
    """

    # If the tensor's volume matches the total volume of all shards and
    # all shard boundaries are within tensor dims, we have a compatible
    # sharding spec for this tensor. Note that we have already verified
    # we don't have overlapping shards.
    tensor_rank = len(tensor_dims)
    shards_rank = len(shards_metadata[0].shard_offsets)
    if tensor_rank != shards_rank:
        raise ValueError(
            f"Rank of tensor is {tensor_rank}, but shards rank is {shards_rank}"
        )

    total_shard_volume = 0
    for shard in shards_metadata:
        #@ invariant total_shard_volume == sum(prod(shards_metadata[j].shard_sizes) for j in range(loop_index()))
        #@ invariant forall j in range(loop_index()) :: all(shards_metadata[j].shard_offsets[k] + shards_metadata[j].shard_sizes[k] <= tensor_dims[k] for k in range(tensor_rank))
        shard_volume = 1
        for i, shard_length in enumerate(shard.shard_sizes):
            #@ invariant shard_volume == prod(shard.shard_sizes[:i])
            #@ invariant forall k in range(i) :: shard.shard_offsets[k] + shard.shard_sizes[k] <= tensor_dims[k]
            #@ proof ProductStep(shard.shard_sizes, i)
            shard_volume *= shard_length
            if shard.shard_offsets[i] + shard.shard_sizes[i] > tensor_dims[i]:
                raise ValueError(
                    f"Shard offset {shard.shard_offsets[i]} and length "
                    f"{shard.shard_sizes[i]} exceeds tensor dim: {tensor_dims[i]} for shard {shard}"
                )
        #@ proof FullProduct(shard.shard_sizes)
        #@ proof SumExtension([prod(shards_metadata[j].shard_sizes) for j in range(loop_index() + 1)], [prod(shards_metadata[j].shard_sizes) for j in range(loop_index())])
        total_shard_volume += shard_volume

    tensor_volume = 1
    for size in tensor_dims:
        #@ invariant tensor_volume == prod(tensor_dims[:loop_index()])
        #@ proof ProductStep(tensor_dims, loop_index())
        tensor_volume *= size

    #@ proof FullProduct(tensor_dims)
    if total_shard_volume != tensor_volume:
        # TODO: Can we improve this error message to point out the gaps?
        raise ValueError(
            f"Total volume of shards: {total_shard_volume} "
            f"does not match tensor volume: {tensor_volume}, in other words "
            f"all the individual shards do not cover the entire tensor"
        )
