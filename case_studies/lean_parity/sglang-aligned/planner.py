from dataclasses import dataclass

@dataclass(frozen=True)
class KVSnapshot:
    kv_committed_len: int
    kv_allocated_len: int

@dataclass(frozen=True)
class RequestSnapshot:
    kv: KVSnapshot

#@ requires page_size > 0
#@ requires reserve >= 0
#@ requires forall j in range(len(reqs)) :: 0 <= reqs[j].kv.kv_committed_len <= reqs[j].kv.kv_allocated_len
#@ requires forall j in range(len(reqs)) :: reqs[j].kv.kv_allocated_len % page_size == 0
#@ ensures len(result[0]) == len(reqs)
#@ ensures len(result[1]) == len(reqs)
#@ ensures forall j in range(len(reqs)) :: result[0][j] == reqs[j].kv.kv_allocated_len
#@ ensures forall j in range(len(reqs)) :: result[1][j] == max(reqs[j].kv.kv_allocated_len, (reqs[j].kv.kv_committed_len + reserve + page_size - 1) // page_size * page_size)
#@ ensures forall j in range(len(reqs)) :: result[1][j] >= result[0][j]
#@ ensures forall j in range(len(reqs)) :: result[1][j] >= reqs[j].kv.kv_committed_len + reserve
#@ ensures forall j in range(len(reqs)) :: result[1][j] % page_size == 0
#@ ensures result[2] == sum(result[1]) - sum(result[0])
#@ ensures result[2] >= 0
def page_aligned_decode_alloc_lens(
    reqs: list[RequestSnapshot],
    *,
    reserve: int,
    page_size: int,
) -> tuple[list[int], list[int], int]:
    """Whole-page decode alloc lens: nxt rounds committed up to page so allocated
    == recorded (unaligned tails leak at ps>1)."""
    cur_kv_lens = [0] * len(reqs)
    nxt_kv_lens = [0] * len(reqs)
    num_needed_tokens = 0
    for i, r in enumerate(reqs):
        #@ invariant len(cur_kv_lens) == len(reqs)
        #@ invariant len(nxt_kv_lens) == len(reqs)
        #@ invariant num_needed_tokens == sum(nxt_kv_lens[:i]) - sum(cur_kv_lens[:i])
        #@ invariant num_needed_tokens >= 0
        #@ invariant forall j in range(i) :: cur_kv_lens[j] == reqs[j].kv.kv_allocated_len
        #@ invariant forall j in range(i) :: nxt_kv_lens[j] == max(reqs[j].kv.kv_allocated_len, (reqs[j].kv.kv_committed_len + reserve + page_size - 1) // page_size * page_size)
        #@ invariant forall j in range(i) :: nxt_kv_lens[j] >= cur_kv_lens[j]
        #@ invariant forall j in range(i) :: nxt_kv_lens[j] >= reqs[j].kv.kv_committed_len + reserve
        #@ invariant forall j in range(i) :: nxt_kv_lens[j] % page_size == 0
        cur = r.kv.kv_allocated_len
        #@ proof AllocationFacts(cur, r.kv.kv_committed_len, reserve, page_size)
        nxt = max(
            cur,
            (r.kv.kv_committed_len + reserve + page_size - 1) // page_size * page_size,
        )
        #@ proof PrefixWriteSum(cur_kv_lens, i, cur)
        cur_kv_lens[i] = cur
        #@ proof PrefixWriteSum(nxt_kv_lens, i, nxt)
        nxt_kv_lens[i] = nxt
        num_needed_tokens += nxt - cur
    #@ proof FullSlice(cur_kv_lens)
    #@ proof FullSlice(nxt_kv_lens)
    return cur_kv_lens, nxt_kv_lens, num_needed_tokens

