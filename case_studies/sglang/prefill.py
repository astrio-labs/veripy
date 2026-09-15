#@ requires sliding_window_size >= 0
#@ requires chunked_prefill_size >= 0
#@ requires page_size > 0
#@ ensures result >= page_size + 2 * sliding_window_size
#@ ensures result >= page_size + 2 * chunked_prefill_size
#@ ensures result == page_size + 2 * sliding_window_size or result == page_size + 2 * chunked_prefill_size
def get_extend_input_len_swa_limit(
    sliding_window_size: int, chunked_prefill_size: int, page_size: int
) -> int:
    # 1. a factor of 2x is because each prefill contains chunked_prefill_size tokens,
    #    and between prefills, we run swa_radix_cache.cache_unfinished_req(),
    #    so we unlock the previously locked nodes.
    # 2. max is to handle the case that chunked_prefill_size is larger than sliding_window_size.
    #    in that case, each prefill contains chunked_prefill_size tokens,
    #    and we can only free out-of-sliding-window kv indices after each prefill.
    # 3. page_size is because we want to have 1 token extra for generated tokens.
    return page_size + 2 * max(sliding_window_size, chunked_prefill_size)
