-- VERIPY LIBRARY arithmetic
theorem CdivPost (a b : Int) (hb : b≠0) : cdiv__post a b (-(a.fdiv (-b))) := by
  have facts:=FloorDivFacts a (-b)
  have eq:=facts.1
  simp only [Int.mul_neg] at eq
  unfold cdiv__post
  simp only [Int.sub_mul,Int.neg_mul,Int.one_mul]
  by_cases positive : 0<b
  · have bound:=facts.2.2.1 (by omega)
    constructor <;> omega
  · have bound:=facts.2.1 (by omega)
    constructor <;> omega

theorem RoundUpPost (x y : Int) (hy : 0<y) : round_up__post x y ((x+y-1).fdiv y*y) := by
  refine ⟨Int.mul_fmod_left _ _,?_⟩
  have facts:=FloorDivFacts (x+y-1) y
  have bound:=facts.2.1 hy
  omega

theorem RoundDownPost (x y : Int) (hy : 0<y) : round_down__post x y (x.fdiv y*y) := by
  refine ⟨Int.mul_fmod_left _ _,?_⟩
  have facts:=FloorDivFacts x y
  have bound:=facts.2.1 hy
  omega

@[spec]
theorem cdiv__proof («a» : Int) («b» : Int) (__vp_h0 : ((«b» ≠ (0 : Int)))) :
  ⦃⌜True⌝⦄ «cdiv» «a» «b» ⦃(fun __vp_result => ⌜(«cdiv__post» «a» «b» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«cdiv__error» «a» «b» __vp_error)⌝, ())⦄ := by
  mvcgen [«cdiv», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
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
    all_goals first | (apply CdivPost;assumption) | omega
  )

@[spec]
theorem round_up__proof («x» : Int) («y» : Int) (__vp_h0 : ((«y» > (0 : Int)))) :
  ⦃⌜True⌝⦄ «round_up» «x» «y» ⦃(fun __vp_result => ⌜(«round_up__post» «x» «y» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«round_up__error» «x» «y» __vp_error)⌝, ())⦄ := by
  mvcgen [«round_up», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
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
    all_goals first | (apply RoundUpPost;assumption) | omega
  )

@[spec]
theorem round_down__proof («x» : Int) («y» : Int) (__vp_h0 : ((«y» > (0 : Int)))) :
  ⦃⌜True⌝⦄ «round_down» «x» «y» ⦃(fun __vp_result => ⌜(«round_down__post» «x» «y» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«round_down__error» «x» «y» __vp_error)⌝, ())⦄ := by
  mvcgen [«round_down», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
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
    all_goals first | (apply RoundDownPost;assumption) | omega
  )
