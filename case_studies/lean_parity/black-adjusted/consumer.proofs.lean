theorem AppendAt [Inhabited α] (xs : List α) (x : α) :
    (xs ++ [x]).getD xs.length default = x := by simp [List.getD_eq_getElem?_getD]

theorem SortedPairs (xs : List (Int × Int)) :
    (xs.mergeSort (fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)))).Perm xs := by
  exact List.mergeSort_perm _ _

theorem FinderInit (line : Int) (mappings : List _LinesMapping) (start : Int)
    (h : 0 ≤ start ∧ start ≤ Int.ofNat mappings.length) :
    _find_lines_mapping_index__inv_27 line mappings start start := by
  unfold _find_lines_mapping_index__inv_27
  exact ⟨⟨Int.le_refl _,h.2⟩,fun k hk => by omega⟩

theorem FinderBounds (line : Int) (mappings : List _LinesMapping) (start i : Int)
    (h : _find_lines_mapping_index__inv_27 line mappings start i) :
    start ≤ i ∧ i ≤ Int.ofNat mappings.length := h.1

theorem FinderFound (line : Int) (mappings : List _LinesMapping) (start i : Int)
    (h : _find_lines_mapping_index__inv_27 line mappings start i)
    (found : (mappings.getD (if i < 0 then Int.ofNat mappings.length+i else i).toNat default).original_start ≤ line ∧
      line ≤ (mappings.getD (if i < 0 then Int.ofNat mappings.length+i else i).toNat default).original_end) :
    _find_lines_mapping_index__post line mappings start i :=
  ⟨h.1,Or.inr found,h.2⟩

theorem FinderEnd (line : Int) (mappings : List _LinesMapping) (start i : Int)
    (h : _find_lines_mapping_index__inv_27 line mappings start i)
    (done : ¬ i < Int.ofNat mappings.length) :
    _find_lines_mapping_index__post line mappings start i :=
  ⟨h.1,Or.inl done,h.2⟩

theorem FinderStep (line : Int) (mappings : List _LinesMapping) (start i : Int)
    (h : _find_lines_mapping_index__inv_27 line mappings start i)
    (bound : i < Int.ofNat mappings.length)
    (miss : ¬ ((mappings.getD (if i < 0 then Int.ofNat mappings.length+i else i).toNat default).original_start ≤ line ∧
      line ≤ (mappings.getD (if i < 0 then Int.ofNat mappings.length+i else i).toNat default).original_end)) :
    _find_lines_mapping_index__inv_27 line mappings start (i+1) := by
  refine ⟨⟨by have := h.1; omega,by omega⟩,?_⟩
  intro k hk
  by_cases he : k=i
  · simpa only [he] using miss
  · exact h.2 k (by omega)

theorem FinderAccess (line : Int) (mappings : List _LinesMapping) (start i : Int)
    (hstart : 0 ≤ start ∧ start ≤ Int.ofNat mappings.length)
    (h : _find_lines_mapping_index__inv_27 line mappings start i)
    (bound : i < Int.ofNat mappings.length)
    (bad : ¬ (0 ≤ (if i < 0 then Int.ofNat mappings.length+i else i) ∧
      (if i < 0 then Int.ofNat mappings.length+i else i) < Int.ofNat mappings.length)) : False := by
  have hb := h.1
  have hn : ¬ i < 0 := by omega
  rw [if_neg hn] at bad
  omega

def AdjustedOrigin (lines : List (Int × Int)) (mappings : List _LinesMapping) (item : Int × Int) : Prop :=
  ∃ lr ∈ lines, ∃ sm ∈ mappings, ∃ em ∈ mappings,
    (sm.original_start ≤ lr.1 ∧ lr.1 ≤ sm.original_end) ∧
    (em.original_start ≤ lr.2 ∧ lr.2 ≤ em.original_end) ∧
    item.1 = (if sm.is_changed_block = true then sm.modified_start else lr.1-sm.original_start+sm.modified_start) ∧
    item.2 = (if em.is_changed_block = true then em.modified_end else lr.2-em.original_start+em.modified_start)

theorem AdjustedInit (lines : List (Int × Int)) (maps : List _LinesMapping) :
    adjusted_lines_from_mappings__inv_46 lines maps [] 0 0 := by
  unfold adjusted_lines_from_mappings__inv_46
  simp
  intro k hk; omega

theorem AdjustedBounds (lines : List (Int × Int)) (maps : List _LinesMapping)
    (output : List (Int × Int)) (cursor i : Int)
    (h : adjusted_lines_from_mappings__inv_46 lines maps output cursor i) :
    0 ≤ cursor ∧ cursor ≤ Int.ofNat maps.length := h.1

theorem AdjustedSkip (lines : List (Int × Int)) (maps : List _LinesMapping)
    (output : List (Int × Int)) (cursor i next : Int)
    (h : adjusted_lines_from_mappings__inv_46 lines maps output cursor i)
    (hb : 0 ≤ next ∧ next ≤ Int.ofNat maps.length) :
    adjusted_lines_from_mappings__inv_46 lines maps output next (i+1) :=
  ⟨hb,by have := h.2.1; omega,h.2.2⟩

theorem AdjustedAppend (lines : List (Int × Int)) (maps : List _LinesMapping)
    (output : List (Int × Int)) (cursor i next : Int) (item : Int × Int)
    (h : adjusted_lines_from_mappings__inv_46 lines maps output cursor i)
    (hb : 0 ≤ next ∧ next ≤ Int.ofNat maps.length)
    (origin : AdjustedOrigin lines maps item) (ordered : item.1 ≤ item.2) :
    adjusted_lines_from_mappings__inv_46 lines maps (output ++ [item]) next (i+1) := by
  refine ⟨hb,by simp; have := h.2.1; omega,?_,?_⟩
  · intro value hv
    rcases List.mem_append.mp hv with hv | hv
    · exact h.2.2.1 value hv
    · have he : value=item := by simpa using hv
      subst value; exact origin
  · intro k hk
    by_cases before : k.toNat < output.length
    · have old := h.2.2.2 k (by change 0 ≤ k ∧ k < (↑output.length : Int); omega)
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_append,if_pos before] using old
    · have he : k.toNat = output.length := by simp at hk; omega
      simpa only [he,AppendAt] using ordered

theorem AdjustedPost (lines : List (Int × Int)) (maps : List _LinesMapping)
    (output : List (Int × Int)) (cursor i : Int)
    (h : adjusted_lines_from_mappings__inv_46 lines maps output cursor i)
    (hi : i = Int.ofNat (lines.mergeSort (fun a b => decide (a.1 < b.1 ∨ a.1=b.1 ∧ a.2≤b.2))).length) :
    adjusted_lines_from_mappings__post lines maps output := by
  have he := (SortedPairs lines).length_eq
  rw [he] at hi
  exact ⟨h.2.2.1,by have := h.2.1; omega,h.2.2.2⟩

theorem ReadMember [Inhabited α] (xs : List α) (i : Int)
    (hb : 0 ≤ i ∧ i < Int.ofNat xs.length) :
    xs.getD (if i < 0 then Int.ofNat xs.length+i else i).toNat default ∈ xs := by
  rw [if_neg (by omega)]
  have hn : i.toNat < xs.length := by change 0 ≤ i ∧ i < (↑xs.length : Int) at hb; omega
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

theorem SortedMember (lines pre suf : List (Int × Int)) (item : Int × Int)
    (h : lines.mergeSort (fun a b => decide (a.1 < b.1 ∨ a.1=b.1 ∧ a.2≤b.2)) = pre ++ item :: suf) :
    item ∈ lines := by
  apply (SortedPairs lines).mem_iff.mp
  rw [h]; simp

theorem AdjustedCommit (lines pre suf : List (Int × Int)) (maps : List _LinesMapping)
    (output : List (Int × Int)) (cursor i next finish : Int) (lr item : Int × Int)
    (h : adjusted_lines_from_mappings__inv_46 lines maps output cursor i)
    (hs : lines.mergeSort (fun a b => decide (a.1 < b.1 ∨ a.1=b.1 ∧ a.2≤b.2)) = pre ++ lr :: suf)
    (hstart : _find_lines_mapping_index__post lr.1 maps cursor next)
    (hend : _find_lines_mapping_index__post lr.2 maps next finish)
    (hn : next < Int.ofNat maps.length) (hf : finish < Int.ofNat maps.length)
    (origin : item =
      ((if (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).is_changed_block = true
        then (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).modified_start
        else lr.1 - (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).original_start + (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).modified_start),
       (if (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).is_changed_block = true
        then (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).modified_end
        else lr.2 - (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).original_start + (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).modified_start)))
    (ordered : item.1 ≤ item.2) :
    adjusted_lines_from_mappings__inv_46 lines maps (output ++ [item]) next (i+1) := by
  have hb := h.1
  have hnb := hstart.1
  have hfb := hend.1
  apply AdjustedAppend lines maps output cursor i next item h (by omega) _ ordered
  refine ⟨lr,SortedMember lines pre suf lr hs,_,ReadMember maps next (by omega),_,ReadMember maps finish (by omega),?_,?_,?_,?_⟩
  · exact hstart.2.1.resolve_left (fun bad => bad hn)
  · exact hend.2.1.resolve_left (fun bad => bad hf)
  · rw [origin]
  · rw [origin]

theorem AdjustedSkipFound (lines : List (Int × Int)) (maps : List _LinesMapping)
    (output : List (Int × Int)) (cursor i next line : Int)
    (h : adjusted_lines_from_mappings__inv_46 lines maps output cursor i)
    (found : _find_lines_mapping_index__post line maps cursor next) :
    adjusted_lines_from_mappings__inv_46 lines maps output next (i+1) := by
  apply AdjustedSkip lines maps output cursor i next h
  have hb:=h.1; have hf:=found.1
  omega

theorem AdjustedCommitObserved (lines pre suf : List (Int × Int)) (maps : List _LinesMapping)
    (output : List (Int × Int)) (cursor i next finish : Int) (lr item : Int × Int)
    (h : adjusted_lines_from_mappings__inv_46 lines maps output cursor i)
    (hs : lines.mergeSort (fun a b => decide (a.1 < b.1 ∨ a.1=b.1 ∧ a.2≤b.2)) = pre ++ lr :: suf)
    (hstart : _find_lines_mapping_index__post lr.1 maps cursor next)
    (hend : _find_lines_mapping_index__post lr.2 maps next finish)
    (hn : next < Int.ofNat maps.length) (hf : finish < Int.ofNat maps.length)
    (origin : item =
      ((if (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).is_changed_block = true
        then (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).modified_start
        else lr.1 - (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).original_start + (maps.getD (if next < 0 then Int.ofNat maps.length+next else next).toNat default).modified_start),
       (if (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).is_changed_block = true
        then (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).modified_end
        else lr.2 - (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).original_start + (maps.getD (if finish < 0 then Int.ofNat maps.length+finish else finish).toNat default).modified_start)))
    (accepted : Bool) (valid : is_valid_line_range__post item accepted) (yes : accepted=true) :
    adjusted_lines_from_mappings__inv_46 lines maps (output ++ [item]) next (i+1) := by
  apply AdjustedCommit lines pre suf maps output cursor i next finish lr item h hs hstart hend hn hf origin
  exact valid.mp yes

@[spec]
theorem is_valid_line_range__proof («lines» : (Int × Int))  :
  ⦃⌜True⌝⦄ «is_valid_line_range» «lines» ⦃(fun __vp_result => ⌜(«is_valid_line_range__post» «lines» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«is_valid_line_range__error» «lines» __vp_error)⌝, ())⦄ := by
  mvcgen [«is_valid_line_range», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
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
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «AdjustedCommitObserved» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «AdjustedCommitObserved» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«is_valid_line_range__post», «is_valid_line_range__error»] | grind (lax := true) [«AdjustedCommitObserved», «is_valid_line_range__post», «is_valid_line_range__error»] | grind (lax := true) [«AdjustedCommitObserved», «AppendAt», «ReadMember», «SortedMember», «SortedPairs», «is_valid_line_range__post», «is_valid_line_range__error»]
  )

@[spec]
theorem _find_lines_mapping_index__proof («original_line» : Int) («lines_mappings» : (List «_LinesMapping»)) («start_index» : Int) (__vp_h0 : (((0 : Int) ≤ «start_index») ∧ («start_index» ≤ (Int.ofNat («lines_mappings»).length)))) :
  ⦃⌜True⌝⦄ «_find_lines_mapping_index» «original_line» «lines_mappings» «start_index» ⦃(fun __vp_result => ⌜(«_find_lines_mapping_index__post» «original_line» «lines_mappings» «start_index» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_find_lines_mapping_index__error» «original_line» «lines_mappings» «start_index» __vp_error)⌝, ())⦄ := by
  mvcgen [«_find_lines_mapping_index», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  case inv1 => exact (by exact fun (_, «index») => ⟨(((Int.ofNat («lines_mappings»).length) - «index»)).toNat⟩)
  case inv2 => exact (by exact (fun __vp_state => match __vp_state with | .inl (__vp_returned, «index») => ⌜__vp_returned = none ∧ («_find_lines_mapping_index__inv_27» «original_line» «lines_mappings» «start_index» «index»)⌝ | .inr (some __vp_return, _) => ⌜«_find_lines_mapping_index__post» «original_line» «lines_mappings» «start_index» __vp_return⌝ | .inr (none, «index») => ⌜(«_find_lines_mapping_index__inv_27» «original_line» «lines_mappings» «start_index» «index») ∧ ¬ ((«index» < (Int.ofNat («lines_mappings»).length)))⌝, fun _ => ⌜False⌝, ()))
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
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «AdjustedCommit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedCommitObserved» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedSkipFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderAccess» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderEnd» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «AdjustedCommit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedCommitObserved» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedSkipFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderAccess» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderEnd» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«_find_lines_mapping_index__post», «_find_lines_mapping_index__error»] | grind (lax := true) [«AdjustedCommit», «AdjustedCommitObserved», «AdjustedSkipFound», «FinderAccess», «FinderBounds», «FinderEnd», «FinderFound», «FinderInit», «FinderStep», «_find_lines_mapping_index__inv_27», «_find_lines_mapping_index__post», «_find_lines_mapping_index__error»] | grind (lax := true) [«AdjustedCommit», «AdjustedCommitObserved», «AdjustedSkipFound», «AppendAt», «FinderAccess», «FinderBounds», «FinderEnd», «FinderFound», «FinderInit», «FinderStep», «ReadMember», «SortedMember», «SortedPairs», «_find_lines_mapping_index__inv_27», «_find_lines_mapping_index__post», «_find_lines_mapping_index__error»]
  )

theorem adjusted_lines_from_mappings__proof («lines» : (List (Int × Int))) («lines_mappings» : (List «_LinesMapping»))  :
  ⦃⌜True⌝⦄ «adjusted_lines_from_mappings» «lines» «lines_mappings» ⦃(fun __vp_result => ⌜(«adjusted_lines_from_mappings__post» «lines» «lines_mappings» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«adjusted_lines_from_mappings__error» «lines» «lines_mappings» __vp_error)⌝, ())⦄ := by
  mvcgen [«adjusted_lines_from_mappings», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 46; exact (by exact ⇓⟨__vp_cursor, «new_lines», «current_mapping_index», «__vp_index_46»⟩ => ⌜(«adjusted_lines_from_mappings__inv_46» «lines» «lines_mappings» «new_lines» «current_mapping_index» «__vp_index_46») ∧ «__vp_index_46» = Int.ofNat __vp_cursor.prefix.length⌝))
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
    all_goals try (solve | apply AdjustedSkipFound <;> assumption)
    all_goals try (solve |
      veripy_cursor lr 46 0 0 0
      veripy_capture new_range
      apply AdjustedCommitObserved lines _ _ lines_mappings _ _ _ _ _ lr new_range
      all_goals first | assumption | (simp only [VeriPy.ofNat_cast];omega) |
        (dsimp (config := { zetaDelta := true }) only at *; simp only [VeriPy.ofNat_cast] at *;grind only))
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «AdjustedAppend» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedCommit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedCommitObserved» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedSkip» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedSkipFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «AdjustedAppend» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedCommit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedCommitObserved» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedSkip» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AdjustedSkipFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«adjusted_lines_from_mappings__post», «adjusted_lines_from_mappings__error»] | grind (lax := true) [«AdjustedAppend», «AdjustedBounds», «AdjustedCommit», «AdjustedCommitObserved», «AdjustedInit», «AdjustedPost», «AdjustedSkip», «AdjustedSkipFound», «adjusted_lines_from_mappings__inv_46», «adjusted_lines_from_mappings__post», «adjusted_lines_from_mappings__error»] | grind (lax := true) [«AdjustedAppend», «AdjustedBounds», «AdjustedCommit», «AdjustedCommitObserved», «AdjustedInit», «AdjustedPost», «AdjustedSkip», «AdjustedSkipFound», «AppendAt», «ReadMember», «SortedMember», «SortedPairs», «is_valid_line_range__post», «is_valid_line_range__error», «_find_lines_mapping_index__post», «_find_lines_mapping_index__error», «adjusted_lines_from_mappings__inv_46», «adjusted_lines_from_mappings__post», «adjusted_lines_from_mappings__error»]
  )
