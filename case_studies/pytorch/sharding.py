#@ requires dim_size >= 0
#@ requires chunks > 0
#@ ensures result >= 0
#@ ensures (result - 1) * chunks < dim_size <= result * chunks
def get_split_size(dim_size: int, chunks: int) -> int:
    """
    Computes the split size inline with ``torch.chunk``

    Args:
        dim_size(int): Size of the dimension being chunked.
        chunks(int): Number of chunks to create for ``dim_size``.

    Returns:
        An int indicating the split size to use.
    """
    #@ proof FloorDivFacts(dim_size + chunks - 1, chunks)
    return (dim_size + chunks - 1) // chunks

#@ requires dim_size >= 0
#@ requires split_size >= 0
#@ requires idx >= 0
#@ ensures 0 <= result <= split_size
#@ ensures result <= dim_size
#@ ensures split_size * idx >= dim_size ==> result == 0
#@ ensures split_size * (idx + 1) <= dim_size ==> result == split_size
#@ ensures split_size * idx < dim_size < split_size * (idx + 1) ==> result == dim_size - split_size * idx
def get_chunked_dim_size(dim_size: int, split_size: int, idx: int) -> int:
    """
    Computes the dim size of the chunk for provided ``idx`` given ``dim_size``
    and ``split_size``.

    Args:
        dim_size(int): Size of the dimension being chunked.
        split_size(int): The chunk size for each chunk of ``dim_size``.
        idx(int): The index of chunk whose dim size is being requested.

    Returns:
        An int indicating the dim size of the chunk.
    """
    return max(min(dim_size, split_size * (idx + 1)) - split_size * idx, 0)
