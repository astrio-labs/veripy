theorem ProductStep (xs : List Int) (i : Int) (h : 0 ≤ i ∧ i < Int.ofNat xs.length) :
    (VeriPy.slice xs 0 (i+1)).prod = (VeriPy.slice xs 0 i).prod * xs.getD i.toNat 0 := by
  have hn : i.toNat < xs.length := by change 0 ≤ i ∧ i < (↑xs.length : Int) at h; omega
  have hi : ¬ i < 0 := by omega
  have his : ¬ i+1 < 0 := by omega
  have he : (i+1).toNat = i.toNat+1 := by omega
  simp only [VeriPy.slice,show ¬ (0:Int)<0 by omega,if_false,hi,his,if_neg,show (0:Int).toNat=0 by rfl,List.drop_zero]
  rw [he,List.take_succ_eq_append_getElem hn]
  simp only [List.prod_append_int,List.prod_cons,List.prod_nil,Int.mul_one,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]

theorem FullProduct (xs : List Int) : (VeriPy.slice xs 0 (Int.ofNat xs.length)).prod = xs.prod := by
  unfold VeriPy.slice
  rw [if_neg (show ¬ (0:Int)<0 by omega),if_neg (show ¬ Int.ofNat xs.length<0 by have hn : 0 ≤ Int.ofNat xs.length := Int.natCast_nonneg _; omega)]
  change (xs.take xs.length).prod=xs.prod
  rw [List.take_length]

theorem SumExtension (pre : List Int) (x : Int) : (pre ++ [x]).sum = pre.sum+x := by
  simp

theorem ReadCursor [Inhabited α] (pre suf : List α) (x : α) :
    (pre ++ x :: suf).getD pre.length default = x := by simp [List.getD_eq_getElem?_getD]

theorem TensorOuterInit (shards : List ShardMetadata) (dims : List Int) (rank srank : Int) :
    check_tensor__inv_36 shards dims rank srank 0 0 := by
  unfold check_tensor__inv_36
  simp [VeriPy.range]
  intro j hj; omega

theorem TensorInnerInit (shards : List ShardMetadata) (dims : List Int) (rank srank total outer : Int) (shard : ShardMetadata) :
    check_tensor__inv_40 shards dims rank srank total outer shard 1 0 := by
  unfold check_tensor__inv_40
  simp [VeriPy.slice]
  intro k hk; omega

theorem TensorVolumeInit (shards : List ShardMetadata) (dims : List Int) (rank srank total : Int) :
    check_tensor__inv_55 shards dims rank srank total 1 0 := by
  simp [check_tensor__inv_55,VeriPy.slice]

theorem TensorInnerStep (shards : List ShardMetadata) (dims : List Int)
    (rank srank total outer volume i size : Int) (shard : ShardMetadata)
    (pre suf : List Int)
    (h : check_tensor__inv_40 shards dims rank srank total outer shard volume i)
    (hs : shard.shard_sizes = pre ++ size :: suf) (hi : i=Int.ofNat pre.length)
    (bound : shard.shard_offsets.getD i.toNat default + shard.shard_sizes.getD i.toNat default ≤ dims.getD i.toNat default) :
    check_tensor__inv_40 shards dims rank srank total outer shard (volume*size) (i+1) := by
  have hb : 0 ≤ i ∧ i < Int.ofNat shard.shard_sizes.length := by rw [hs,hi]; simp; omega
  have hv := ProductStep shard.shard_sizes i hb
  have hr : shard.shard_sizes.getD i.toNat 0 = size := by
    rw [hs,hi]; change (pre ++ size :: suf).getD pre.length default = size
    exact ReadCursor pre suf size
  refine ⟨?_,?_⟩
  · rw [hv,hr,←h.1]
  · intro k hk
    by_cases he : k=i
    · simpa only [he] using bound
    · exact h.2 k (by omega)

theorem TensorVolumeStep (shards : List ShardMetadata) (dims : List Int)
    (rank srank total volume i size : Int) (pre suf : List Int)
    (h : check_tensor__inv_55 shards dims rank srank total volume i)
    (hs : dims=pre++size::suf) (hi : i=Int.ofNat pre.length) :
    check_tensor__inv_55 shards dims rank srank total (volume*size) (i+1) := by
  have hb : 0 ≤ i ∧ i < Int.ofNat dims.length := by rw [hs,hi]; simp; omega
  have hv := ProductStep dims i hb
  have hr : dims.getD i.toNat 0 = size := by rw [hs,hi]; exact ReadCursor pre suf size
  change volume*size=(VeriPy.slice dims 0 (i+1)).prod
  rw [hv,hr]; exact congrArg (fun x => x*size) h

theorem RangeExtension (i : Int) (hi : 0 ≤ i) : VeriPy.range 0 (i+1) = VeriPy.range 0 i ++ [i] := by
  have he : (i+1-0).toNat = (i-0).toNat+1 := by omega
  simp only [VeriPy.range,he,List.range_succ,List.map_append,List.map_cons,List.map_nil]
  have hc : Int.ofNat (i-0).toNat=i := by simpa using Int.toNat_of_nonneg hi
  rw [hc]; simp only [Int.zero_add]

theorem TensorOuterStep (shards pre suf : List ShardMetadata) (dims : List Int)
    (rank srank total i volume : Int) (shard : ShardMetadata)
    (h : check_tensor__inv_36 shards dims rank srank total i)
    (hs : shards=pre++shard::suf) (hi : i=Int.ofNat pre.length)
    (hv : volume=shard.shard_sizes.prod)
    (bounds : ∀ k : Int, 0 ≤ k ∧ k < rank →
      shard.shard_offsets.getD k.toNat default + shard.shard_sizes.getD k.toNat default ≤ dims.getD k.toNat default) :
    check_tensor__inv_36 shards dims rank srank (total+volume) (i+1) := by
  have hi0 : 0 ≤ i := by rw [hi]; exact Int.natCast_nonneg _
  have hr : shards.getD i.toNat default=shard := by rw [hs,hi]; exact ReadCursor pre suf shard
  refine ⟨?_,?_⟩
  · change total+volume=((VeriPy.range 0 (i+1)).map (fun j => (shards.getD j.toNat default).shard_sizes.prod)).sum
    rw [RangeExtension i hi0,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Int.add_zero,hr]
    rw [←h.1,hv]
  · intro j hj k hk
    by_cases he : j=i
    · subst j; rw [hr]; exact bounds k hk
    · exact h.2 j (by omega) k hk

theorem TensorRankError (shards : List ShardMetadata) (dims : List Int)
    (bad : Int.ofNat dims.length ≠ Int.ofNat (shards.getD 0 default).shard_offsets.length) :
    check_tensor__error shards dims VeriPy.Error.value := by
  refine ⟨rfl,⟨fun _ => Or.inl ?_,fun _ => trivial⟩⟩
  exact bad

theorem TensorPost (shards : List ShardMetadata) (dims : List Int) (rank srank total volume : Int)
    (outer : check_tensor__inv_36 shards dims rank srank total (Int.ofNat shards.length))
    (last : check_tensor__inv_55 shards dims rank srank total volume (Int.ofNat dims.length))
    (hrank : rank=Int.ofNat dims.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (equal : total=volume) : check_tensor__post shards dims () := by
  have hv : volume=dims.prod := by change volume=(VeriPy.slice dims 0 (Int.ofNat dims.length)).prod at last; rw [FullProduct] at last; exact last
  refine ⟨False.elim,?_⟩
  intro bad
  rcases bad with bad | bad | bad
  · exact bad same
  · apply bad; simpa only [hrank] using outer.2
  · exact bad (by rw [←outer.1,equal,hv])

theorem TensorVolumeError (shards : List ShardMetadata) (dims : List Int) (rank srank total volume : Int)
    (outer : check_tensor__inv_36 shards dims rank srank total (Int.ofNat shards.length))
    (last : check_tensor__inv_55 shards dims rank srank total volume (Int.ofNat dims.length))
    (bad : total ≠ volume) : check_tensor__error shards dims VeriPy.Error.value := by
  have hv : volume=dims.prod := by change volume=(VeriPy.slice dims 0 (Int.ofNat dims.length)).prod at last; rw [FullProduct] at last; exact last
  refine ⟨rfl,⟨fun _ => Or.inr (Or.inr ?_),fun _ => trivial⟩⟩
  intro he; apply bad; rw [outer.1,hv]; exact he

theorem ShardRankCursor (shards pre suf : List ShardMetadata) (dims : List Int) (shard : ShardMetadata)
    (hs : shards=pre++shard::suf)
    (ranks : ∀ j : Int, 0 ≤ j ∧ j < Int.ofNat shards.length →
      Int.ofNat (shards.getD j.toNat default).shard_offsets.length = Int.ofNat (shards.getD 0 default).shard_offsets.length ∧
      Int.ofNat (shards.getD j.toNat default).shard_sizes.length = Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length) :
    shard.shard_offsets.length=dims.length ∧ shard.shard_sizes.length=dims.length := by
  have hb : 0 ≤ Int.ofNat pre.length ∧ Int.ofNat pre.length < Int.ofNat shards.length := by rw [hs]; simp; omega
  have hr := ranks (Int.ofNat pre.length) hb
  have read : shards.getD (Int.ofNat pre.length).toNat default=shard := by rw [hs]; exact ReadCursor pre suf shard
  rw [read,←same] at hr
  exact ⟨Int.ofNat.inj hr.1,Int.ofNat.inj hr.2⟩

theorem TensorBoundError (shards pre suf : List ShardMetadata) (dims : List Int) (shard : ShardMetadata) (i : Int)
    (hs : shards=pre++shard::suf) (hb : 0 ≤ i ∧ i < Int.ofNat dims.length)
    (bad : shard.shard_offsets.getD i.toNat default + shard.shard_sizes.getD i.toNat default > dims.getD i.toNat default) :
    check_tensor__error shards dims VeriPy.Error.value := by
  refine ⟨rfl,⟨fun _ => Or.inr (Or.inl ?_),fun _ => trivial⟩⟩
  intro hall
  have hj : 0 ≤ Int.ofNat pre.length ∧ Int.ofNat pre.length < Int.ofNat shards.length := by rw [hs]; simp; omega
  have h := hall (Int.ofNat pre.length) hj i hb
  have read : shards.getD (Int.ofNat pre.length).toNat default=shard := by rw [hs]; exact ReadCursor pre suf shard
  rw [read] at h
  omega

theorem TensorOuterFinished (shards pre suf : List ShardMetadata) (dims : List Int)
    (rank srank total i volume inner : Int) (shard : ShardMetadata)
    (h : check_tensor__inv_36 shards dims rank srank total i)
    (hs : shards=pre++shard::suf) (hi : i=Int.ofNat pre.length)
    (hin : check_tensor__inv_40 shards dims rank srank total (i+1) shard volume inner)
    (done : inner=Int.ofNat shard.shard_sizes.length)
    (ranks : ∀ j : Int, 0 ≤ j ∧ j < Int.ofNat shards.length →
      Int.ofNat (shards.getD j.toNat default).shard_offsets.length = Int.ofNat (shards.getD 0 default).shard_offsets.length ∧
      Int.ofNat (shards.getD j.toNat default).shard_sizes.length = Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (hrank : rank=Int.ofNat dims.length) :
    check_tensor__inv_36 shards dims rank srank (total+volume) (i+1) := by
  have lengths:=ShardRankCursor shards pre suf dims shard hs ranks same
  apply TensorOuterStep shards pre suf dims rank srank total i volume shard h hs hi
  · have hv:=hin.1; rw [done,FullProduct] at hv; exact hv
  · have hb:=hin.2
    rw [done,lengths.2,←hrank] at hb
    exact hb

theorem TensorPostCursor (shards : List ShardMetadata) (dims : List Int) (rank srank total volume i j : Int)
    (outer : check_tensor__inv_36 shards dims rank srank total i)
    (last : check_tensor__inv_55 shards dims rank srank total volume j)
    (hi : i=Int.ofNat shards.length) (hj : j=Int.ofNat dims.length)
    (hrank : rank=Int.ofNat dims.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (equal : total=volume) : check_tensor__post shards dims () := by
  rw [hi] at outer; rw [hj] at last
  exact TensorPost shards dims rank srank total volume outer last hrank same equal

theorem TensorVolumeErrorCursor (shards : List ShardMetadata) (dims : List Int) (rank srank total volume i j : Int)
    (outer : check_tensor__inv_36 shards dims rank srank total i)
    (last : check_tensor__inv_55 shards dims rank srank total volume j)
    (hi : i=Int.ofNat shards.length) (hj : j=Int.ofNat dims.length)
    (bad : total ≠ volume) : check_tensor__error shards dims VeriPy.Error.value := by
  rw [hi] at outer; rw [hj] at last
  exact TensorVolumeError shards dims rank srank total volume outer last bad


theorem TensorCursorSafety (shards pre suf : List ShardMetadata) (dims : List Int) (shard : ShardMetadata)
    (before after : List Int) (size i : Int)
    (hs : shards=pre++shard::suf) (hsize : shard.shard_sizes=before++size::after)
    (hi : i=Int.ofNat before.length)
    (ranks : ∀ j : Int, 0 ≤ j ∧ j < Int.ofNat shards.length →
      Int.ofNat (shards.getD j.toNat default).shard_offsets.length = Int.ofNat (shards.getD 0 default).shard_offsets.length ∧
      Int.ofNat (shards.getD j.toNat default).shard_sizes.length = Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length) :
    0 ≤ i ∧ i < Int.ofNat shard.shard_offsets.length ∧ i < Int.ofNat shard.shard_sizes.length ∧ i < Int.ofNat dims.length := by
  have hr:=ShardRankCursor shards pre suf dims shard hs ranks same
  have hb : 0 ≤ i ∧ i < Int.ofNat shard.shard_sizes.length := by rw [hsize,hi]; simp; omega
  rw [hr.1,hr.2] at *
  exact ⟨hb.1,hb.2,hb.2,hb.2⟩


theorem TensorOffsetsInvalid (shards pre suf : List ShardMetadata) (dims : List Int) (shard : ShardMetadata)
    (before after : List Int) (size i : Int)
    (hs : shards=pre++shard::suf) (hsize : shard.shard_sizes=before++size::after)
    (hi : i=Int.ofNat before.length)
    (ranks : ∀ j : Int, 0 ≤ j ∧ j < Int.ofNat shards.length →
      Int.ofNat (shards.getD j.toNat default).shard_offsets.length = Int.ofNat (shards.getD 0 default).shard_offsets.length ∧
      Int.ofNat (shards.getD j.toNat default).shard_sizes.length = Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (bad : ¬ (0 ≤ i ∧ i < Int.ofNat shard.shard_offsets.length)) : False := by
  have hb:=TensorCursorSafety shards pre suf dims shard before after size i hs hsize hi ranks same
  omega


theorem TensorSizesInvalid (shards pre suf : List ShardMetadata) (dims : List Int) (shard : ShardMetadata)
    (before after : List Int) (size i : Int)
    (hs : shards=pre++shard::suf) (hsize : shard.shard_sizes=before++size::after)
    (hi : i=Int.ofNat before.length)
    (ranks : ∀ j : Int, 0 ≤ j ∧ j < Int.ofNat shards.length →
      Int.ofNat (shards.getD j.toNat default).shard_offsets.length = Int.ofNat (shards.getD 0 default).shard_offsets.length ∧
      Int.ofNat (shards.getD j.toNat default).shard_sizes.length = Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (bad : ¬ (0 ≤ i ∧ i < Int.ofNat shard.shard_sizes.length)) : False := by
  have hb:=TensorCursorSafety shards pre suf dims shard before after size i hs hsize hi ranks same
  omega


theorem TensorDimsInvalid (shards pre suf : List ShardMetadata) (dims : List Int) (shard : ShardMetadata)
    (before after : List Int) (size i : Int)
    (hs : shards=pre++shard::suf) (hsize : shard.shard_sizes=before++size::after)
    (hi : i=Int.ofNat before.length)
    (ranks : ∀ j : Int, 0 ≤ j ∧ j < Int.ofNat shards.length →
      Int.ofNat (shards.getD j.toNat default).shard_offsets.length = Int.ofNat (shards.getD 0 default).shard_offsets.length ∧
      Int.ofNat (shards.getD j.toNat default).shard_sizes.length = Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (same : Int.ofNat dims.length=Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (bad : ¬ (0 ≤ i ∧ i < Int.ofNat dims.length)) : False := by
  have hb:=TensorCursorSafety shards pre suf dims shard before after size i hs hsize hi ranks same
  omega

theorem check_tensor__proof («shards_metadata» : (List «ShardMetadata»)) («tensor_dims» : (List Int)) (__vp_h0 : (((Int.ofNat («shards_metadata»).length) > (0 : Int)))) (__vp_h1 : (∀ «j» : Int, (0 ≤ «j» ∧ «j» < (Int.ofNat («shards_metadata»).length)) → ((((Int.ofNat ((((«shards_metadata»).getD («j»).toNat default)).«shard_offsets»).length) = (Int.ofNat ((((«shards_metadata»).getD ((0 : Int)).toNat default)).«shard_offsets»).length))) ∧ (((Int.ofNat ((((«shards_metadata»).getD («j»).toNat default)).«shard_sizes»).length) = (Int.ofNat ((((«shards_metadata»).getD ((0 : Int)).toNat default)).«shard_offsets»).length)))))) :
  ⦃⌜True⌝⦄ «check_tensor» «shards_metadata» «tensor_dims» ⦃(fun __vp_result => ⌜(«check_tensor__post» «shards_metadata» «tensor_dims» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«check_tensor__error» «shards_metadata» «tensor_dims» __vp_error)⌝, ())⦄ := by
  mvcgen [«check_tensor», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 36; exact (by (first | veripy_capture «tensor_rank» | veripy_let «tensor_rank» := (Int.ofNat («tensor_dims»).length) | veripy_capture_type «tensor_rank» : Int); (first | veripy_capture «shards_rank» | veripy_let «shards_rank» := (Int.ofNat ((((«shards_metadata»).getD ((0 : Int)).toNat default)).«shard_offsets»).length) | veripy_capture_type «shards_rank» : Int); exact (fun ⟨__vp_cursor, «total_shard_volume», «__vp_index_36»⟩ => ⌜(«check_tensor__inv_36» «shards_metadata» «tensor_dims» «tensor_rank» «shards_rank» «total_shard_volume» «__vp_index_36») ∧ «__vp_index_36» = Int.ofNat __vp_cursor.prefix.length⌝, fun __vp_error => ⌜(«check_tensor__error» «shards_metadata» «tensor_dims» __vp_error)⌝, ())))
  all_goals try (veripy_loop_tag 40; exact (by (first | veripy_capture «tensor_rank» | veripy_let «tensor_rank» := (Int.ofNat («tensor_dims»).length) | veripy_capture_type «tensor_rank» : Int); (first | veripy_capture «shards_rank» | veripy_let «shards_rank» := (Int.ofNat ((((«shards_metadata»).getD ((0 : Int)).toNat default)).«shard_offsets»).length) | veripy_capture_type «shards_rank» : Int); (first | veripy_capture «total_shard_volume» | veripy_let «total_shard_volume» := (0 : Int) | veripy_capture_type «total_shard_volume» : Int); (first | veripy_capture «__vp_index_36» | veripy_capture_type «__vp_index_36» : Int); (first | veripy_capture «shard» | veripy_cursor «shard» 36 0 0 0 | veripy_capture_type «shard» : «ShardMetadata»); exact (fun ⟨__vp_cursor, «shard_volume», «__vp_index_40»⟩ => ⌜(«check_tensor__inv_40» «shards_metadata» «tensor_dims» «tensor_rank» «shards_rank» «total_shard_volume» «__vp_index_36» «shard» «shard_volume» «__vp_index_40») ∧ «__vp_index_40» = Int.ofNat __vp_cursor.prefix.length⌝, fun __vp_error => ⌜(«check_tensor__error» «shards_metadata» «tensor_dims» __vp_error)⌝, ())))
  all_goals try (veripy_loop_tag 55; exact (by (first | veripy_capture «tensor_rank» | veripy_let «tensor_rank» := (Int.ofNat («tensor_dims»).length) | veripy_capture_type «tensor_rank» : Int); (first | veripy_capture «shards_rank» | veripy_let «shards_rank» := (Int.ofNat ((((«shards_metadata»).getD ((0 : Int)).toNat default)).«shard_offsets»).length) | veripy_capture_type «shards_rank» : Int); (first | veripy_capture «total_shard_volume» | veripy_let «total_shard_volume» := (0 : Int) | veripy_capture_type «total_shard_volume» : Int); exact (fun ⟨__vp_cursor, «tensor_volume», «__vp_index_55»⟩ => ⌜(«check_tensor__inv_55» «shards_metadata» «tensor_dims» «tensor_rank» «shards_rank» «total_shard_volume» «tensor_volume» «__vp_index_55») ∧ «__vp_index_55» = Int.ofNat __vp_cursor.prefix.length⌝, fun __vp_error => ⌜(«check_tensor__error» «shards_metadata» «tensor_dims» __vp_error)⌝, ())))
  all_goals (
    try veripy_clear_aux
    try (simp only [VeriPy.loopTag, decide_eq_true_eq, WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_mergeSort, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals try veripy_continue_facts
    all_goals try veripy_project_facts
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals try veripy_fold_projections
    all_goals try (simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.not_ofNat_neg, if_false, Int.toNat_natCast] at *)
    all_goals try (solve |
      veripy_cursor shard 36 0 0 0
      veripy_cursor size 40 0 0 0
      have safe:=TensorCursorSafety shards_metadata _ _ tensor_dims shard _ _ size _ (by assumption) (by assumption) (by assumption) __vp_h1 (by simp only [VeriPy.ofNat_cast];omega)
      dsimp only [shard,size] at safe
      simp only [VeriPy.ofNat_cast] at safe
      grind only)
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «FullProduct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ProductStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeExtension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ShardRankCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SumExtension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorBoundError» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorCursorSafety» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorDimsInvalid» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorInnerInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorInnerStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOffsetsInvalid» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOuterFinished» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOuterInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOuterStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorPostCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorRankError» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorSizesInvalid» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeError» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeErrorCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «FullProduct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ProductStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeExtension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ShardRankCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SumExtension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorBoundError» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorCursorSafety» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorDimsInvalid» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorInnerInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorInnerStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOffsetsInvalid» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOuterFinished» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOuterInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorOuterStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorPostCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorRankError» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorSizesInvalid» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeError» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeErrorCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TensorVolumeStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«check_tensor__post», «check_tensor__error»] | grind (lax := true) [«TensorBoundError», «TensorInnerInit», «TensorInnerStep», «TensorOuterFinished», «TensorOuterInit», «TensorOuterStep», «TensorPost», «TensorPostCursor», «TensorRankError», «TensorVolumeError», «TensorVolumeErrorCursor», «TensorVolumeInit», «TensorVolumeStep», «check_tensor__inv_36», «check_tensor__inv_55», «check_tensor__inv_40», «check_tensor__post», «check_tensor__error»] | grind (lax := true) [«FullProduct», «ProductStep», «RangeExtension», «ReadCursor», «ShardRankCursor», «SumExtension», «TensorBoundError», «TensorCursorSafety», «TensorDimsInvalid», «TensorInnerInit», «TensorInnerStep», «TensorOffsetsInvalid», «TensorOuterFinished», «TensorOuterInit», «TensorOuterStep», «TensorPost», «TensorPostCursor», «TensorRankError», «TensorSizesInvalid», «TensorVolumeError», «TensorVolumeErrorCursor», «TensorVolumeInit», «TensorVolumeStep», «check_tensor__inv_36», «check_tensor__inv_55», «check_tensor__inv_40», «check_tensor__post», «check_tensor__error»]
  )
