-- VERIPY LIBRARY arithmetic
theorem AlignedMultiples (b : Int) : ∀ q : Int, (q*b).fmod b=0 := fun q=>Int.mul_fmod_left q b

theorem CeilPost (x y : Int) (hy : 0<y) : ceil_div__post x y ((x+y-1).fdiv y) := by
  have facts:=FloorDivFacts (x+y-1) y
  have bound:=facts.2.1 hy
  unfold ceil_div__post
  simp only [Int.sub_mul,Int.one_mul]
  omega

theorem AlignPost (x y q : Int) (hy : 0<y) (post : ceil_div__post x y q) : ceil_align__post x y (q*y) := by
  refine ⟨Int.mul_fmod_left _ _,?_⟩
  unfold ceil_div__post at post
  simp only [Int.sub_mul,Int.one_mul] at post
  omega

@[spec]
theorem ceil_div__proof («x» : Int) («y» : Int) (__vp_h0 : ((«y» > (0 : Int)))) :
  ⦃⌜True⌝⦄ «ceil_div» «x» «y» ⦃(fun __vp_result => ⌜(«ceil_div__post» «x» «y» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«ceil_div__error» «x» «y» __vp_error)⌝, ())⦄ := by
  mvcgen [«ceil_div», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
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
    all_goals first | (apply CeilPost <;> assumption) | omega
  )

@[spec]
theorem ceil_align__proof («x» : Int) («y» : Int) (__vp_h0 : ((«y» > (0 : Int)))) :
  ⦃⌜True⌝⦄ «ceil_align» «x» «y» ⦃(fun __vp_result => ⌜(«ceil_align__post» «x» «y» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«ceil_align__error» «x» «y» __vp_error)⌝, ())⦄ := by
  mvcgen [«ceil_align», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
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
    all_goals first | (apply AlignPost <;> assumption) | omega
  )
