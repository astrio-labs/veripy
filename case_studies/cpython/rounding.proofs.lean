-- VERIPY LIBRARY arithmetic
theorem NearestPost (a b : Int) (hb : b≠0) :
    _divide_and_round__post a b
      (if (if b>0 then 2*a.fmod b>b else 2*a.fmod b<b) ∨ 2*a.fmod b=b ∧ (a.fdiv b).fmod 2=1
        then a.fdiv b+1 else a.fdiv b) := by
  have facts:=FloorDivFacts a b
  have decomposition:=facts.1
  unfold _divide_and_round__post
  simp only [Int.fmod_eq_emod_of_nonneg _ (by decide : (0:Int)≤2)]
  by_cases positive : b>0
  · have bounds:=facts.2.1 positive
    simp only [if_pos positive]
    split <;> (try simp only [Int.add_mul,Int.one_mul]) <;> omega
  · have bounds:=facts.2.2.1 (by omega)
    simp only [if_neg positive]
    split <;> (try simp only [Int.add_mul,Int.one_mul]) <;> omega

@[spec]
theorem _divide_and_round__proof («a» : Int) («b» : Int) (__vp_h0 : ((«b» ≠ (0 : Int)))) :
  ⦃⌜True⌝⦄ «_divide_and_round» «a» «b» ⦃(fun __vp_result => ⌜(«_divide_and_round__post» «a» «b» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_divide_and_round__error» «a» «b» __vp_error)⌝, ())⦄ := by
  mvcgen [«_divide_and_round», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
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
    all_goals try omega
  )
  all_goals have nearest:=NearestPost a b __vp_h0
  all_goals split at nearest <;> grind only
