-- VERIPY LIBRARY ranges
theorem PairInit (a b : ShardMetadata) (n : Int) :
    _check_shard_metadata_pair_overlap__inv_20 a b n 0 := by
  unfold _check_shard_metadata_pair_overlap__inv_20
  intro j hj; omega

theorem PairStep (a b : ShardMetadata) (n i : Int)
    (h : _check_shard_metadata_pair_overlap__inv_20 a b n i)
    (left : ¬ a.shard_offsets.getD i.toNat default ≥ b.shard_offsets.getD i.toNat default + b.shard_sizes.getD i.toNat default)
    (right : ¬ b.shard_offsets.getD i.toNat default ≥ a.shard_offsets.getD i.toNat default + a.shard_sizes.getD i.toNat default) :
    _check_shard_metadata_pair_overlap__inv_20 a b n (i+1) := by
  intro j hj
  by_cases he : j = i
  · subst j; constructor <;> omega
  · exact h j (by omega)

theorem PairPost (a b : ShardMetadata) (n : Int)
    (h : _check_shard_metadata_pair_overlap__inv_20 a b n (Int.ofNat a.shard_offsets.length)) :
    _check_shard_metadata_pair_overlap__post a b true := by
  unfold _check_shard_metadata_pair_overlap__post
  constructor
  · intro _; simpa only [_check_shard_metadata_pair_overlap__inv_20, Int.zero_add] using h
  · intro _; rfl


theorem RangeLength (n : Nat) : (VeriPy.range 0 (Int.ofNat n)).length = n := by
  simp [VeriPy.range]

theorem PairStepCursor (a b : ShardMetadata) (n cur i : Int) (pre suf : List Int)
    (hr : VeriPy.range 0 n = pre ++ cur :: suf) (hi : i = Int.ofNat pre.length)
    (h : _check_shard_metadata_pair_overlap__inv_20 a b n i)
    (left : ¬ a.shard_offsets.getD cur.toNat default ≥ b.shard_offsets.getD cur.toNat default + b.shard_sizes.getD cur.toNat default)
    (right : ¬ b.shard_offsets.getD cur.toNat default ≥ a.shard_offsets.getD cur.toNat default + a.shard_sizes.getD cur.toNat default) :
    _check_shard_metadata_pair_overlap__inv_20 a b n (i+1) := by
  have he : cur = i := (RangeCursor n cur pre suf hr).1.trans hi.symm
  subst cur
  exact PairStep a b n i h left right

theorem RangeFailure (n cur : Int) (pre suf : List Int)
    (h : VeriPy.range 0 n = pre ++ cur :: suf)
    (bad : ¬ (0 ≤ cur ∧ cur < n)) : False := by
  exact bad (RangeCursor n cur pre suf h).2
