-- VERIPY LIBRARY allocation
theorem PrefixWriteNat (xs : List Int) (i : Nat) (v : Int) (hi : i < xs.length) :
    ((xs.set i v).take (i+1)).sum = (xs.take i).sum + v := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have h := ih i (by simpa using hi)
      simp only [List.set, List.take, List.sum_cons] at *
      omega

theorem PrefixWriteSum (xs : List Int) (i v : Int) (hi : 0 ≤ i) (hb : i < xs.length) :
    (VeriPy.slice (xs.set i.toNat v) 0 (i+1)).sum = (VeriPy.slice xs 0 i).sum + v := by
  have h := PrefixWriteNat xs i.toNat v (by omega)
  have he : (i+1).toNat = i.toNat+1 := by omega
  simpa [VeriPy.slice, show ¬i < 0 by omega, show ¬i+1 < 0 by omega, he] using h

theorem FullSlice (xs : List Int) : VeriPy.slice xs 0 xs.length = xs := by
  simp [VeriPy.slice, show ¬(xs.length : Int) < 0 by omega]

theorem EmptySlice (xs : List Int) : VeriPy.slice xs 0 0 = [] := by
  simp [VeriPy.slice]

theorem ReadBefore [Inhabited α] (xs : List α) (i j : Int) (v : α)
    (hj : 0 ≤ j) (hji : j < i) :
    (xs.set i.toNat v).getD j.toNat default = xs.getD j.toNat default := by
  rw [ReadWrite]
  simp [show i.toNat ≠ j.toNat by omega]

theorem ReadSame [Inhabited α] (xs : List α) (i : Int) (v : α)
    (hi : 0 ≤ i) (hb : i < xs.length) :
    (xs.set i.toNat v).getD i.toNat default = v := by
  rw [ReadWrite]
  simp [show i.toNat < xs.length by omega]

theorem PlannerStep (reqs pre suf : List RequestSnapshot) (r : RequestSnapshot)
    (reserve p total i : Int) (cur nxt : List Int)
    (hp : p > 0) (hr : reqs = pre ++ r :: suf) (hi : i = pre.length)
    (halign : ∀ j : Int, 0 ≤ j → j < Int.ofNat reqs.length →
      (reqs.getD j.toNat default).kv.kv_allocated_len.fmod p = 0)
    (hinv : page_aligned_decode_alloc_lens__inv_36 reqs reserve p cur nxt total i) :
    page_aligned_decode_alloc_lens__inv_36 reqs reserve p
      (cur.set i.toNat r.kv.kv_allocated_len)
      (nxt.set i.toNat (max r.kv.kv_allocated_len ((r.kv.kv_committed_len + reserve + p - 1).fdiv p * p)))
      (total + (max r.kv.kv_allocated_len ((r.kv.kv_committed_len + reserve + p - 1).fdiv p * p) - r.kv.kv_allocated_len))
      (i+1) := by
  rcases hinv with ⟨hc, hn, ht, ht0, hcur, hnxt, hge, hcomm, hmod⟩
  have hcl : cur.length = reqs.length := Int.ofNat.inj hc
  have hnl : nxt.length = reqs.length := Int.ofNat.inj hn
  have hi0 : 0 ≤ i := by omega
  have hib : i < reqs.length := by simp [hr, hi]; omega
  have hic : i < cur.length := by omega
  have hin : i < nxt.length := by omega
  have hread : reqs.getD i.toNat default = r := by
    rw [hr, hi]
    simpa using ReadCursor pre suf r
  have hrmod := halign i hi0 hib
  rw [hread] at hrmod
  have hf := AllocationFacts r.kv.kv_allocated_len r.kv.kv_committed_len reserve p hp
  unfold page_aligned_decode_alloc_lens__inv_36
  refine ⟨by simpa using hc, by simpa using hn, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PrefixWriteSum _ _ _ hi0 hin, PrefixWriteSum _ _ _ hi0 hic]
    omega
  · rintro j ⟨hj0, hj⟩
    by_cases hji : j = i
    · subst j
      rw [ReadSame _ _ _ hi0 hic, hread]
    · rw [ReadBefore _ _ _ _ hj0 (by omega)]
      exact hcur j ⟨hj0, by omega⟩
  · rintro j ⟨hj0, hj⟩
    by_cases hji : j = i
    · subst j
      rw [ReadSame _ _ _ hi0 hin, hread]
    · rw [ReadBefore _ _ _ _ hj0 (by omega)]
      exact hnxt j ⟨hj0, by omega⟩
  · rintro j ⟨hj0, hj⟩
    by_cases hji : j = i
    · subst j
      rw [ReadSame _ _ _ hi0 hin, ReadSame _ _ _ hi0 hic]
      exact hf.1
    · rw [ReadBefore _ _ _ _ hj0 (by omega), ReadBefore _ _ _ _ hj0 (by omega)]
      exact hge j ⟨hj0, by omega⟩
  · rintro j ⟨hj0, hj⟩
    by_cases hji : j = i
    · subst j
      rw [ReadSame _ _ _ hi0 hin, hread]
      exact hf.2.1
    · rw [ReadBefore _ _ _ _ hj0 (by omega)]
      exact hcomm j ⟨hj0, by omega⟩
  · rintro j ⟨hj0, hj⟩
    by_cases hji : j = i
    · subst j
      rw [ReadSame _ _ _ hi0 hin]
      rcases hf.2.2 with he | hm
      · rw [he]; exact hrmod
      · exact hm
    · rw [ReadBefore _ _ _ _ hj0 (by omega)]
      exact hmod j ⟨hj0, by omega⟩

theorem PlannerInit (reqs : List RequestSnapshot) (reserve p : Int) :
    page_aligned_decode_alloc_lens__inv_36 reqs reserve p
      (List.replicate reqs.length 0) (List.replicate reqs.length 0) 0 0 := by
  simp [page_aligned_decode_alloc_lens__inv_36, EmptySlice]
  repeat' first | apply And.intro | intro
  all_goals omega

theorem PlannerLengths (reqs : List RequestSnapshot) (reserve p : Int)
    (cur nxt : List Int) (total i : Int)
    (h : page_aligned_decode_alloc_lens__inv_36 reqs reserve p cur nxt total i) :
    cur.length = reqs.length ∧ nxt.length = reqs.length := by
  exact ⟨Int.ofNat.inj h.1, Int.ofNat.inj h.2.1⟩

theorem PlannerPost (reqs : List RequestSnapshot) (reserve p : Int)
    (cur nxt : List Int) (total : Int)
    (h : page_aligned_decode_alloc_lens__inv_36 reqs reserve p cur nxt total reqs.length) :
    page_aligned_decode_alloc_lens__post reqs reserve p (cur,nxt,total) := by
  have hl := PlannerLengths reqs reserve p cur nxt total reqs.length h
  rcases h with ⟨hc,hn,ht,ht0,hcur,hnxt,hge,hcomm,hmod⟩
  unfold page_aligned_decode_alloc_lens__post
  have hsc : VeriPy.slice cur 0 reqs.length = cur := by rw [←hl.1];exact FullSlice cur
  have hsn : VeriPy.slice nxt 0 reqs.length = nxt := by rw [←hl.2];exact FullSlice nxt
  rw [hsc,hsn] at ht
  exact ⟨hc,hn,hcur,hnxt,hge,hcomm,hmod,ht,ht0⟩

theorem PlannerFailureCur (reqs pre suf : List RequestSnapshot) (r : RequestSnapshot)
    (reserve p total i : Int) (cur nxt : List Int)
    (hr : reqs = pre ++ r :: suf) (hi : i = pre.length)
    (h : page_aligned_decode_alloc_lens__inv_36 reqs reserve p cur nxt total i)
    (bad : ¬(0 ≤ i ∧ i < cur.length)) : False := by
  have hl := PlannerLengths reqs reserve p cur nxt total i h
  have hn : reqs.length = pre.length + 1 + suf.length := by simp [hr];omega
  omega

theorem PlannerFailureNext (reqs pre suf : List RequestSnapshot) (r : RequestSnapshot)
    (reserve p total i : Int) (cur nxt : List Int)
    (hr : reqs = pre ++ r :: suf) (hi : i = pre.length)
    (h : page_aligned_decode_alloc_lens__inv_36 reqs reserve p cur nxt total i)
    (bad : ¬(0 ≤ i ∧ i < nxt.length)) : False := by
  have hl := PlannerLengths reqs reserve p cur nxt total i h
  have hn : reqs.length = pre.length + 1 + suf.length := by simp [hr];omega
  omega

theorem RequestLoopTag (reqs : List RequestSnapshot) (tag : Nat) : VeriPy.loopTag tag reqs=reqs := rfl

theorem page_aligned_decode_alloc_lens__proof («reqs» : (List «RequestSnapshot»)) («reserve» : Int) («page_size» : Int) (__vp_h0 : ((«page_size» > (0 : Int)))) (__vp_h1 : ((«reserve» ≥ (0 : Int)))) (__vp_h2 : (∀ «j» : Int, (0 ≤ «j» ∧ «j» < (Int.ofNat («reqs»).length)) → (((0 : Int) ≤ ((((«reqs»).getD («j»).toNat default)).«kv»).«kv_committed_len») ∧ (((((«reqs»).getD («j»).toNat default)).«kv»).«kv_committed_len» ≤ ((((«reqs»).getD («j»).toNat default)).«kv»).«kv_allocated_len»)))) (__vp_h3 : (∀ «j» : Int, (0 ≤ «j» ∧ «j» < (Int.ofNat («reqs»).length)) → (((Int.fmod ((((«reqs»).getD («j»).toNat default)).«kv»).«kv_allocated_len» «page_size») = (0 : Int))))) :
  ⦃⌜True⌝⦄ «page_aligned_decode_alloc_lens» «reqs» «reserve» «page_size» ⦃(fun __vp_result => ⌜(«page_aligned_decode_alloc_lens__post» «reqs» «reserve» «page_size» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«page_aligned_decode_alloc_lens__error» «reqs» «reserve» «page_size» __vp_error)⌝, ())⦄ := by
  mvcgen [«page_aligned_decode_alloc_lens», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 36; exact (by exact ⇓⟨__vp_cursor, «cur_kv_lens», «nxt_kv_lens», «num_needed_tokens», «__vp_index_36»⟩ => ⌜(«page_aligned_decode_alloc_lens__inv_36» «reqs» «reserve» «page_size» «cur_kv_lens» «nxt_kv_lens» «num_needed_tokens» «__vp_index_36») ∧ «__vp_index_36» = Int.ofNat __vp_cursor.prefix.length⌝))
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
    all_goals first | (solve | apply PlannerStep <;> first | assumption | (simp only [VeriPy.ofNat_cast];omega) | (exact fun j hj hb => __vp_h3 j ⟨hj,hb⟩)) | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «AllocationFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «EmptySlice» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FullSlice» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerFailureCur» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerFailureNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerLengths» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PrefixWriteNat» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PrefixWriteSum» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadBefore» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadSame» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadWrite» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «AllocationFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «EmptySlice» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FullSlice» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerFailureCur» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerFailureNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerLengths» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PlannerStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PrefixWriteNat» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PrefixWriteSum» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadBefore» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadSame» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadWrite» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«page_aligned_decode_alloc_lens__post», «page_aligned_decode_alloc_lens__error»] | grind (lax := true) [«PlannerFailureCur», «PlannerFailureNext», «PlannerInit», «PlannerLengths», «PlannerPost», «PlannerStep», «page_aligned_decode_alloc_lens__inv_36», «page_aligned_decode_alloc_lens__post», «page_aligned_decode_alloc_lens__error»] | grind (lax := true) [«AllocationFacts», «EmptySlice», «FullSlice», «PlannerFailureCur», «PlannerFailureNext», «PlannerInit», «PlannerLengths», «PlannerPost», «PlannerStep», «PrefixWriteNat», «PrefixWriteSum», «ReadBefore», «ReadCursor», «ReadSame», «ReadWrite», «page_aligned_decode_alloc_lens__inv_36», «page_aligned_decode_alloc_lens__post», «page_aligned_decode_alloc_lens__error»]
  )
