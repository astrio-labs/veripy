def ContainsLine (mapping : _LinesMapping) (line : Int) : Bool :=
  decide (mapping.original_start≤line ∧ line≤mapping.original_end)

def Find (mappings : List _LinesMapping) (line start : Int) : Int :=
  start+Int.ofNat ((mappings.drop start.toNat).findIdx (fun m=>ContainsLine m line))

def Emit (mappings : List _LinesMapping) (lr : Int × Int) (si ei : Int) : List (Int × Int) :=
  if si=Int.ofNat mappings.length ∨ ei=Int.ofNat mappings.length then [] else
  let sm:=mappings.getD si.toNat default
  let em:=mappings.getD ei.toNat default
  let a:=if sm.is_changed_block then sm.modified_start else lr.1-sm.original_start+sm.modified_start
  let b:=if em.is_changed_block then em.modified_end else lr.2-em.original_start+em.modified_start
  if a≤b then [(a,b)] else []

def State (lines : List (Int × Int)) (mappings : List _LinesMapping) : Nat → Int × List (Int × Int)
  | 0 => (0,[])
  | n+1 =>
    let previous:=State lines mappings n
    let lr:=lines.getD n default
    let si:=Find mappings lr.1 previous.1
    let ei:=Find mappings lr.2 si
    (si,previous.2++Emit mappings lr si ei)

def Expected (lines : List (Int × Int)) (mappings : List _LinesMapping) : List (Int × Int) :=
  (State (lines.mergeSort (fun a b=>decide (a.1<b.1 ∨ a.1=b.1 ∧ a.2≤b.2))) mappings lines.length).2

def Progress (lines : List (Int × Int)) (mappings : List _LinesMapping) (n cursor : Int) (output : List (Int × Int)) : Prop :=
  (0≤n ∧ n≤Int.ofNat lines.length) ∧ State lines mappings n.toNat=(cursor,output)

-- VERIPY PRELUDE END
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


theorem LookupNat (xs : List α) (predicate : α → Bool) (i : Nat) (bound : i≤xs.length)
    (miss : ∀ j, (hj : j<i) → predicate (xs[j]'(by omega))=false)
    (found : (hi : i<xs.length) → predicate xs[i]=true) : xs.findIdx predicate=i := by
  by_cases inside : i<xs.length
  · exact (List.findIdx_eq inside).mpr ⟨found inside,miss⟩
  · have ending : i=xs.length := by omega
    rw [ending]
    apply List.findIdx_eq_length.mpr
    intro x hx
    obtain ⟨j,hj,he⟩:=List.mem_iff_getElem.mp hx
    have hm:=miss j (by omega)
    simpa only [he] using hm

theorem LookupExact (mappings : List _LinesMapping) (line start index : Int)
    (valid : 0≤start ∧ start≤Int.ofNat mappings.length)
    (post : _find_lines_mapping_index__post line mappings start index) : index=Find mappings line start := by
  have bounds:=post.1
  have nonnegative : 0≤index := by omega
  have delta : 0≤index-start := by omega
  have bound : (index-start).toNat≤(mappings.drop start.toNat).length := by
    simp only [List.length_drop,VeriPy.ofNat_cast] at *;omega
  have read (j : Nat) (hj : j<(mappings.drop start.toNat).length) :
      (mappings.drop start.toNat)[j] = mappings.getD (start+Int.ofNat j).toNat default := by
    have natindex : (start+Int.ofNat j).toNat=start.toNat+j := by
      simp only [VeriPy.ofNat_cast];omega
    have inside : start.toNat+j<mappings.length := by simp only [List.length_drop] at hj;omega
    simp only [List.getElem_drop,natindex,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
  have find : (mappings.drop start.toNat).findIdx (fun m=>ContainsLine m line)=(index-start).toNat := by
    apply LookupNat _ _ _ bound
    · intro j hj
      have good : start≤start+Int.ofNat j ∧ start+Int.ofNat j<index := by
        simp only [VeriPy.ofNat_cast] at *;omega
      have missed:=post.2.2 (start+Int.ofNat j) good
      have nonneg : ¬start+Int.ofNat j<0 := by simp only [VeriPy.ofNat_cast];omega
      rw [read j (by omega)]
      simp only [ContainsLine,decide_eq_false_iff_not]
      simpa only [if_neg nonneg] using missed
    · intro hi
      have inside : index<Int.ofNat mappings.length := by simp only [List.length_drop,VeriPy.ofNat_cast] at *;omega
      have hit:=post.2.1.resolve_left (by omega)
      have sum : start+Int.ofNat (index-start).toNat=index := by simp only [VeriPy.ofNat_cast];omega
      rw [read _ hi,sum]
      simp only [ContainsLine,decide_eq_true_eq]
      simpa only [if_neg (show ¬index<0 by omega)] using hit
  unfold Find
  rw [find]
  simp only [VeriPy.ofNat_cast]
  omega

theorem PairEta (lines pref suff : List (Int × Int)) (a b k : Int)
    (cursor : lines=pref++(a,b)::suff) (index : k=Int.ofNat pref.length) :
    0≤k ∧ k<Int.ofNat lines.length ∧ lines.getD k.toNat default=(a,b) := by
  have natindex : k.toNat=pref.length := by rw [index];rfl
  refine ⟨?_,?_,?_⟩
  · rw [index];exact Int.natCast_nonneg _
  · rw [cursor,index];simp only [List.length_append,List.length_cons,VeriPy.ofNat_cast,Int.natCast_add,Int.natCast_one];omega
  · rw [natindex,cursor];simp [List.getD_eq_getElem?_getD]

theorem Advance (lines : List (Int × Int)) (mappings : List _LinesMapping) (k cursor si ei : Int) (out : List (Int × Int))
    (progress : Progress lines mappings k cursor out)
    (bound : k<Int.ofNat lines.length) (valid : 0≤cursor ∧ cursor≤Int.ofNat mappings.length)
    (start : _find_lines_mapping_index__post (lines.getD k.toNat default).1 mappings cursor si)
    (finish : _find_lines_mapping_index__post (lines.getD k.toNat default).2 mappings si ei) :
    Progress lines mappings (k+1) si (out++Emit mappings (lines.getD k.toNat default) si ei) := by
  have se:=LookupExact mappings _ cursor si valid start
  have ee:=LookupExact mappings _ si ei ⟨by have h:=start.1;omega,start.1.2⟩ finish
  have natstep : (k+1).toNat=k.toNat+1 := by have h:=progress.1;omega
  refine ⟨⟨by have h:=progress.1;omega,by omega⟩,?_⟩
  rw [natstep,State,progress.2]
  simp only [←se,←ee]

theorem Complete (lines : List (Int × Int)) (mappings : List _LinesMapping) (cursor : Int) (out : List (Int × Int))
    (progress : Progress (lines.mergeSort (fun a b=>decide (a.1<b.1 ∨ a.1=b.1 ∧ a.2≤b.2))) mappings (Int.ofNat lines.length) cursor out) :
    out=Expected lines mappings := by
  exact (congrArg Prod.snd progress.2).symm

theorem EmitBound (mappings : List _LinesMapping) (lr : Int × Int) (si ei : Int) :
    (Emit mappings lr si ei).length≤1 ∧ ∀ v∈Emit mappings lr si ei, v.1≤v.2 := by
  unfold Emit
  split
  · simp
  · dsimp only
    split <;> simp_all
    all_goals split <;> try simp_all
    all_goals split <;> try simp_all

theorem ConsumerAdvance (lines : List (Int × Int)) (mappings : List _LinesMapping) (pref suff : List (Int × Int))
    (a b k cursor si ei : Int) (out result : List (Int × Int))
    (inv : adjusted_lines_from_mappings__inv_45 lines mappings out cursor k)
    (iter : lines.mergeSort (fun a b=>decide (a.1<b.1 ∨ a.1=b.1 ∧ a.2≤b.2))=pref++(a,b)::suff)
    (index : k=Int.ofNat pref.length)
    (start : _find_lines_mapping_index__post a mappings cursor si)
    (finish : _find_lines_mapping_index__post b mappings si ei)
    (emit : result=out++Emit mappings (a,b) si ei) :
    adjusted_lines_from_mappings__inv_45 lines mappings result si (k+1) := by
  have bounds:=PairEta _ pref suff a b k iter index
  have step:=Advance _ mappings k cursor si ei out inv.1 bounds.2.1 inv.2.1 (by simpa only [bounds.2.2] using start) (by simpa only [bounds.2.2] using finish)
  rw [bounds.2.2,←emit] at step
  refine ⟨step,⟨by have h:=start.1;have h0:=inv.2.1;omega,start.1.2⟩,?_,?_⟩
  · rw [emit,List.length_append]
    have limited:=(EmitBound mappings (a,b) si ei).1
    have before:=inv.2.2.1
    simp only [VeriPy.ofNat_cast,Int.natCast_add] at *;omega
  · intro j hj
    have member : result.getD j.toNat default∈result := by
      have h : j.toNat<result.length := by simp only [VeriPy.ofNat_cast] at hj;omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
      exact List.getElem_mem h
    rw [emit] at member
    rcases List.mem_append.mp member with old | new
    · obtain ⟨n,hn,he⟩:=List.mem_iff_getElem.mp old
      have good:=inv.2.2.2 (Int.ofNat n) (by simp only [VeriPy.ofNat_cast];omega)
      simpa only [emit,VeriPy.ofNat_cast,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some,he] using good
    · simpa only [emit] using (EmitBound mappings (a,b) si ei).2 _ new

theorem ConsumerInit (lines : List (Int × Int)) (mappings : List _LinesMapping) :
    adjusted_lines_from_mappings__inv_45 lines mappings [] 0 0 := by
  refine ⟨⟨⟨by omega,Int.natCast_nonneg _⟩,rfl⟩,⟨by omega,Int.natCast_nonneg _⟩,by decide,?_⟩
  intro k hk
  simp only [List.length_nil,VeriPy.ofNat_cast] at hk
  omega

theorem ExposeEmpty (mappings : List _LinesMapping) (lr : Int × Int) (si ei : Int)
    (empty : si=Int.ofNat mappings.length ∨ ei=Int.ofNat mappings.length) : Emit mappings lr si ei=[] := by
  simp only [Emit,if_pos empty]

theorem ExposeEmit (mappings : List _LinesMapping) (lr : Int × Int) (si ei : Int)
    (hs : 0≤si ∧ si<Int.ofNat mappings.length) (he : 0≤ei ∧ ei<Int.ofNat mappings.length) :
    Emit mappings lr si ei =
      let sm:=mappings.getD (if si<0 then Int.ofNat mappings.length+si else si).toNat default
      let em:=mappings.getD (if ei<0 then Int.ofNat mappings.length+ei else ei).toNat default
      let a:=if sm.is_changed_block then sm.modified_start else lr.1-sm.original_start+sm.modified_start
      let b:=if em.is_changed_block then em.modified_end else lr.2-em.original_start+em.modified_start
      if a≤b then [(a,b)] else [] := by
  simp only [Emit,if_neg (show ¬(si=Int.ofNat mappings.length ∨ ei=Int.ofNat mappings.length) by omega),
    if_neg (show ¬si<0 by omega),if_neg (show ¬ei<0 by omega)]

theorem CheckNext (lines : List (Int × Int)) (mappings : List _LinesMapping) (k cursor : Int) (out : List (Int × Int))
    (progress : Progress lines mappings k cursor out) : Progress lines mappings k cursor out := progress

theorem ConsumerComplete (lines : List (Int × Int)) (mappings : List _LinesMapping) (out : List (Int × Int)) (cursor k : Int)
    (inv : adjusted_lines_from_mappings__inv_45 lines mappings out cursor k)
    (count : k=Int.ofNat lines.length) :
    adjusted_lines_from_mappings__post lines mappings out ∧ out=Expected lines mappings := by
  refine ⟨⟨by have h:=inv.2.2.1;omega,inv.2.2.2⟩,?_⟩
  apply Complete lines mappings cursor out
  simpa only [count] using inv.1

theorem EmitValues (mappings : List _LinesMapping) (lr value : Int × Int) (si ei : Int)
    (hs : 0≤si ∧ si<Int.ofNat mappings.length) (he : 0≤ei ∧ ei<Int.ofNat mappings.length)
    (start : value.1=if (mappings.getD (if si<0 then Int.ofNat mappings.length+si else si).toNat default).is_changed_block then
      (mappings.getD (if si<0 then Int.ofNat mappings.length+si else si).toNat default).modified_start else
      lr.1-(mappings.getD (if si<0 then Int.ofNat mappings.length+si else si).toNat default).original_start+(mappings.getD (if si<0 then Int.ofNat mappings.length+si else si).toNat default).modified_start)
    (finish : value.2=if (mappings.getD (if ei<0 then Int.ofNat mappings.length+ei else ei).toNat default).is_changed_block then
      (mappings.getD (if ei<0 then Int.ofNat mappings.length+ei else ei).toNat default).modified_end else
      lr.2-(mappings.getD (if ei<0 then Int.ofNat mappings.length+ei else ei).toNat default).original_start+(mappings.getD (if ei<0 then Int.ofNat mappings.length+ei else ei).toNat default).modified_start) :
    Emit mappings lr si ei=if value.1≤value.2 then [value] else [] := by
  rw [ExposeEmit mappings lr si ei hs he]
  dsimp only
  rw [←start,←finish]

theorem EmitAccepted (mappings : List _LinesMapping) (lr value : Int × Int) (si ei : Int) (valid : Bool)
    (emitted : Emit mappings lr si ei=if value.1≤value.2 then [value] else [])
    (post : is_valid_line_range__post value valid) (yes : valid=true) : Emit mappings lr si ei=[value] := by
  rw [emitted,if_pos (post.mp yes)]

theorem EmitRejected (mappings : List _LinesMapping) (lr value : Int × Int) (si ei : Int) (valid : Bool)
    (emitted : Emit mappings lr si ei=if value.1≤value.2 then [value] else [])
    (post : is_valid_line_range__post value valid) (no : ¬valid=true) : Emit mappings lr si ei=[] := by
  rw [emitted,if_neg (fun h=>no (post.mpr h))]

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
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderAccess» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderEnd» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupExact» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupNat» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderAccess» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderEnd» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupExact» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupNat» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«is_valid_line_range__post», «is_valid_line_range__error»] | grind (lax := true) [«is_valid_line_range__post», «is_valid_line_range__error»] | grind (lax := true) [«AppendAt», «FinderAccess», «FinderBounds», «FinderEnd», «FinderFound», «FinderInit», «FinderStep», «LookupExact», «LookupNat», «SortedPairs», «is_valid_line_range__post», «is_valid_line_range__error»]
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
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderAccess» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderEnd» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupExact» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupNat» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «AppendAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderAccess» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderBounds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderEnd» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FinderStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupExact» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LookupNat» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«_find_lines_mapping_index__post», «_find_lines_mapping_index__error»] | grind (lax := true) [«_find_lines_mapping_index__inv_27», «_find_lines_mapping_index__post», «_find_lines_mapping_index__error»] | grind (lax := true) [«AppendAt», «FinderAccess», «FinderBounds», «FinderEnd», «FinderFound», «FinderInit», «FinderStep», «LookupExact», «LookupNat», «SortedPairs», «_find_lines_mapping_index__inv_27», «_find_lines_mapping_index__post», «_find_lines_mapping_index__error»]
  )

@[spec]
theorem adjusted_lines_from_mappings_exact («lines» : (List (Int × Int))) («lines_mappings» : (List «_LinesMapping»))  :
  ⦃⌜True⌝⦄ «adjusted_lines_from_mappings» «lines» «lines_mappings» ⦃(fun __vp_result => ⌜(«adjusted_lines_from_mappings__post» «lines» «lines_mappings» __vp_result) ∧ __vp_result=Expected lines lines_mappings⌝, fun (__vp_error : VeriPy.Error) => ⌜(«adjusted_lines_from_mappings__error» «lines» «lines_mappings» __vp_error)⌝, ())⦄ := by
  mvcgen [«adjusted_lines_from_mappings», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 45; exact (by exact ⇓⟨__vp_cursor, «new_lines», «current_mapping_index», «__vp_index_45»⟩ => ⌜(«adjusted_lines_from_mappings__inv_45» «lines» «lines_mappings» «new_lines» «current_mapping_index» «__vp_index_45») ∧ «__vp_index_45» = Int.ofNat __vp_cursor.prefix.length⌝))
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
    all_goals try (first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega)
  )

  try (case' vc25.pre.left => exact ConsumerInit lines lines_mappings)
  try (case' vc26.post.success.left => exact (ConsumerComplete lines lines_mappings _ _ _ (by assumption) (by assumption)).1)
  try (case' vc26.post.success.right => exact (ConsumerComplete lines lines_mappings _ _ _ (by assumption) (by assumption)).2)
  all_goals try (solve |
    veripy_cursor firstLine 45 0 0 2
    veripy_cursor lastLine 45 0 1 2
    apply ConsumerAdvance lines lines_mappings _ _ firstLine lastLine
    all_goals first | assumption | (simp only [VeriPy.ofNat_cast];omega) | rfl |
      (dsimp only [firstLine,lastLine]
       first
       | (rw [ExposeEmpty]; simp; simp only [VeriPy.ofNat_cast];omega)
       | (rw [EmitAccepted]
          all_goals try assumption
          all_goals try simp only [List.append_nil]
          all_goals try rfl
          veripy_capture new_range
          apply EmitValues _ _ new_range
          all_goals first | (simp only [VeriPy.ofNat_cast];omega) |
            (dsimp (config := { zetaDelta := true }) only at *; simp only [VeriPy.ofNat_cast] at *; grind only))
       | (rw [EmitRejected]
          all_goals try assumption
          all_goals try simp only [List.append_nil]
          all_goals try rfl
          veripy_capture new_range
          apply EmitValues _ _ new_range
          all_goals first | (simp only [VeriPy.ofNat_cast];omega) |
            (dsimp (config := { zetaDelta := true }) only at *; simp only [VeriPy.ofNat_cast] at *; grind only))))


theorem adjusted_lines_from_mappings__proof (lines : List (Int × Int)) (lines_mappings : List _LinesMapping) :
  ⦃⌜True⌝⦄ adjusted_lines_from_mappings lines lines_mappings ⦃(fun result => ⌜adjusted_lines_from_mappings__post lines lines_mappings result⌝, fun error => ⌜adjusted_lines_from_mappings__error lines lines_mappings error⌝, ())⦄ := by
  apply Triple.entails_wp_of_post (adjusted_lines_from_mappings_exact lines lines_mappings)
  constructor
  · intro result;exact And.left
  · exact ExceptConds.entails.rfl
