def MappingEmit (blocks : List Match) (i : Nat) : List _LinesMapping :=
  let block := blocks.getD i default
  let gap := if i=0 then
      if block.a≠0 ∨ block.b≠0 then [_LinesMapping.mk 1 block.a 1 block.b false] else []
    else
      let previous := blocks.getD (i-1) default
      [_LinesMapping.mk (previous.a+previous.size+1) block.a (previous.b+previous.size+1) block.b true]
  gap ++ if i+1<blocks.length then [_LinesMapping.mk (block.a+1) (block.a+block.size) (block.b+1) (block.b+block.size) false] else []

def MappingPrefix (blocks : List Match) (n : Nat) : List _LinesMapping := (List.range n).flatMap (MappingEmit blocks)

def MappingProgress (blocks : List Match) (i : Int) (result : List _LinesMapping) : Prop := result=MappingPrefix blocks i.toNat

-- VERIPY PRELUDE END

theorem MappingStep (blocks : List Match) (n : Nat) :
    MappingPrefix blocks (n+1)=MappingPrefix blocks n++MappingEmit blocks n := by
  simp only [MappingPrefix,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem MappingComplete (blocks : List Match) (result : List _LinesMapping)
    (progress : MappingProgress blocks (Int.ofNat blocks.length) result) : result=MappingPrefix blocks blocks.length := progress

theorem MappingEmitBound (blocks : List Match) (i : Nat) : (MappingEmit blocks i).length≤2 := by
  unfold MappingEmit
  split <;> simp_all only [List.length_append,List.length_cons,List.length_nil]
  all_goals split <;> simp_all only [List.length_append,List.length_cons,List.length_nil]
  all_goals try (split <;> simp_all only [List.length_append,List.length_cons,List.length_nil])
  all_goals omega

theorem MappingCursor (blocks pref suff : List Match) (cur : Match) (k : Int)
    (cursor : blocks=pref++cur::suff) (index : k=Int.ofNat pref.length) :
    0≤k ∧ k<Int.ofNat blocks.length ∧ blocks.getD k.toNat default=cur := by
  have hk : k.toNat=pref.length := by rw [index];rfl
  refine ⟨?_,?_,?_⟩
  · rw [index];exact Int.natCast_nonneg _
  · rw [cursor,index];simp only [List.length_append,List.length_cons,VeriPy.ofNat_cast,Int.natCast_add,Int.natCast_one];omega
  · rw [hk,cursor];simp [List.getD_eq_getElem?_getD]

theorem MappingAdvance (blocks pref suff : List Match) (cur : Match) (k : Int)
    (out result : List _LinesMapping)
    (inv : mappings_from_blocks__inv_26 blocks out k)
    (cursor : blocks=pref++cur::suff) (index : k=Int.ofNat pref.length)
    (emitted : result=out++MappingEmit blocks k.toNat) :
    mappings_from_blocks__inv_26 blocks result (k+1) := by
  have bounds:=MappingCursor blocks pref suff cur k cursor index
  have step : (k+1).toNat=k.toNat+1 := by omega
  refine ⟨?_,?_⟩
  · rw [emitted,List.length_append]
    have limited:=MappingEmitBound blocks k.toNat
    have before:=inv.1
    simp only [VeriPy.ofNat_cast,Int.natCast_add] at *
    omega
  · change result=MappingPrefix blocks (k+1).toNat
    rw [step,MappingStep,←inv.2]
    exact emitted

theorem MappingEmitCursor (blocks pref suff : List Match) (cur : Match) (k : Int)
    (cursor : blocks=pref++cur::suff) (index : k=Int.ofNat pref.length) :
    MappingEmit blocks k.toNat =
      (if k=0 then
        if cur.a≠0 ∨ cur.b≠0 then [_LinesMapping.mk 1 cur.a 1 cur.b false] else []
       else let previous := blocks.getD (if k-1<0 then Int.ofNat blocks.length+(k-1) else k-1).toNat default
            [_LinesMapping.mk (previous.a+previous.size+1) cur.a (previous.b+previous.size+1) cur.b true]) ++
      (if k<Int.ofNat blocks.length-1 then [_LinesMapping.mk (cur.a+1) (cur.a+cur.size) (cur.b+1) (cur.b+cur.size) false] else []) := by
  have hc:=MappingCursor blocks pref suff cur k cursor index
  have zero : k.toNat=0 ↔ k=0 := by omega
  have last : k.toNat+1<blocks.length ↔ k<Int.ofNat blocks.length-1 := by
    simp only [VeriPy.ofNat_cast] at *;omega
  simp only [MappingEmit,hc.2.2,zero,last]
  by_cases first : k=0
  · simp only [first,if_true]
  · have nonnegative : ¬k-1<0 := by omega
    have sub : (k-1).toNat=k.toNat-1 := by omega
    simp only [first,if_false,nonnegative,sub]

@[spec]
theorem mappings_from_blocks_exact («matching_blocks» : (List «Match»))  :
  ⦃⌜True⌝⦄ «mappings_from_blocks» «matching_blocks» ⦃(fun __vp_result => ⌜(«mappings_from_blocks__post» «matching_blocks» __vp_result) ∧ __vp_result=MappingPrefix matching_blocks matching_blocks.length⌝, fun (__vp_error : VeriPy.Error) => ⌜(«mappings_from_blocks__error» «matching_blocks» __vp_error)⌝, ())⦄ := by
  mvcgen [«mappings_from_blocks», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 26; exact (by exact ⇓⟨__vp_cursor, «lines_mappings», «__vp_index_26»⟩ => ⌜(«mappings_from_blocks__inv_26» «matching_blocks» «lines_mappings» «__vp_index_26») ∧ «__vp_index_26» = Int.ofNat __vp_cursor.prefix.length⌝))
  all_goals (
    try veripy_clear_aux
    try (simp only [VeriPy.loopTag, decide_eq_true_eq, WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals try veripy_continue_facts
    all_goals try veripy_project_facts
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals try veripy_fold_projections
    all_goals try (simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.not_ofNat_neg, if_false, Int.toNat_natCast] at *)
    all_goals try (first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega)
  )

  all_goals try (
    veripy_cursor block 26 0 0 0
    veripy_cursor position 26 1 0 0
    have emitted := MappingEmitCursor matching_blocks _ _ block position (by assumption) rfl
    dsimp only [block, position] at emitted
    first
      | (solve | apply MappingAdvance <;> first | assumption | (simp only [VeriPy.ofNat_cast];omega) | grind only)
      | (solve | have bounds := MappingCursor matching_blocks _ _ block position (by assumption) rfl; dsimp only [block,position] at bounds; simp only [VeriPy.ofNat_cast] at bounds; grind only)
  )
  try (case' vc12.pre.left => simp [mappings_from_blocks__inv_26,MappingProgress,MappingPrefix])
  all_goals try (grind [mappings_from_blocks__inv_26,mappings_from_blocks__post,MappingProgress])

theorem mappings_from_blocks__proof («matching_blocks» : (List «Match»))  :
  ⦃⌜True⌝⦄ «mappings_from_blocks» «matching_blocks» ⦃(fun __vp_result => ⌜(«mappings_from_blocks__post» «matching_blocks» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«mappings_from_blocks__error» «matching_blocks» __vp_error)⌝, ())⦄ := by
  apply Triple.entails_wp_of_post (mappings_from_blocks_exact matching_blocks)
  constructor
  · intro result
    exact And.left
  · exact ExceptConds.entails.rfl
