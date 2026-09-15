theorem RangeCursor (lo hi cur : Int) (pre suf : List Int)
    (h : VeriPy.range lo hi = pre ++ cur :: suf) :
    cur = lo + Int.ofNat pre.length ∧ lo ≤ cur ∧ cur < hi := by
  have hl : pre.length < (hi-lo).toNat := by
    have he := congrArg List.length h
    simp [VeriPy.range] at he
    omega
  have hr : (VeriPy.range lo hi).getD pre.length 0 = cur := by
    rw [h]; simp [List.getD_eq_getElem?_getD]
  have hv : (VeriPy.range lo hi).getD pre.length 0 = lo + Int.ofNat pre.length := by
    simp [VeriPy.range, List.getD_eq_getElem?_getD, hl]
  rw [hv] at hr
  have hb : Int.ofNat pre.length < hi-lo := Int.lt_of_toNat_lt (by simpa using hl)
  refine ⟨hr.symm,?_,?_⟩
  · rw [←hr]; exact Int.le_add_of_nonneg_right (Int.natCast_nonneg _)
  · rw [←hr]
    have ha := Int.add_lt_add_left hb lo
    have he : lo + (hi-lo) = hi := by omega
    rw [he] at ha
    exact ha

theorem RangeLength (lo hi : Int) : (VeriPy.range lo hi).length = (hi-lo).toNat := by
  simp [VeriPy.range]

theorem ModPadding (x d : Int) (h : d ≠ 0) :
    (do return (← VeriPy.mod (d - (← VeriPy.mod x d)) d) : Except VeriPy.Error Int) =
      Except.ok ((d - x.fmod d).fmod d) := by
  simp [VeriPy.mod,h]
  rfl

theorem Nonpositive (xs : List Int) :
    xs.any (fun x => decide (x ≤ 0)) = true ↔ ∃ x ∈ xs, x ≤ 0 := by simp

def Padding (values : List Int) (d : Int) : Int :=
  (values.map (fun x => (d - x.fmod d).fmod d)).sum

theorem MinimumInit (values : List Int) (lower : Option Int) (lo hi : Int)
    (hlo : 1 ≤ lo) (hhi : ¬ lo > hi) :
    _approximate_gcd__inv_33 values lower lo hi lo none 0 := by
  unfold _approximate_gcd__inv_33
  simp
  omega

theorem MinimumChoose (values : List Int) (lower : Option Int) (lo hi best i d candidate : Int)
    (previous : Option Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hi0 : 0 ≤ i) (hd : d = lo+i) (hbound : d ≤ hi)
    (hcost : candidate = Padding values d)
    (choose : previous = none ∨ candidate < previous.getD 0 ∨ candidate = previous.getD 0 ∧ d > best) :
    _approximate_gcd__inv_33 values lower lo hi d (some candidate) (i+1) := by
  rcases h with ⟨bounds,initial,prior,price,minimum,tie⟩
  refine ⟨⟨bounds.1,by omega,hbound⟩,?_,?_,?_,?_,?_⟩
  · constructor
    · intro impossible; cases impossible
    · intro impossible; omega
  · right; omega
  · right; exact hcost
  · right
    intro c hc
    by_cases equal : c = d
    · subst c; change candidate ≤ Padding values d; omega
    · cases previous with
      | none =>
        have hz := initial.mp rfl
        omega
      | some previous =>
        have hle : candidate ≤ previous := by
          simp only [reduceCtorEq, false_or, Option.getD_some] at choose
          omega
        have oldmin := minimum.resolve_left (by simp)
        have hcold : lo ≤ c ∧ c < lo+i := by omega
        exact Int.le_trans hle (oldmin c hcold)
  · right
    intro c hc
    right
    omega

theorem MinimumSkip (values : List Int) (lower : Option Int) (lo hi best i d candidate : Int)
    (previous : Option Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hi0 : 0 ≤ i) (hd : d = lo+i)
    (hcost : candidate = Padding values d)
    (skip : ¬(previous = none ∨ candidate < previous.getD 0 ∨ candidate = previous.getD 0 ∧ d > best)) :
    _approximate_gcd__inv_33 values lower lo hi best previous (i+1) := by
  cases previous with
  | none => exact False.elim (skip (Or.inl rfl))
  | some previous =>
    rcases h with ⟨bounds,initial,prior,price,minimum,tie⟩
    have hp := prior.resolve_left (by simp)
    have hmin := minimum.resolve_left (by simp)
    have htie := tie.resolve_left (by simp)
    have hgt : previous < candidate := by
      simp only [reduceCtorEq, false_or, Option.getD_some] at skip
      omega
    refine ⟨bounds,?_,?_,price,?_,?_⟩
    · constructor
      · intro impossible; cases impossible
      · intro impossible; omega
    · right; omega
    · right
      intro c hc
      by_cases he : c = d
      · subst c; change previous ≤ Padding values d; rw [←hcost]; omega
      · exact hmin c (by omega)
    · right
      intro c hc
      by_cases he : c = d
      · subst c; left; change ¬previous = Padding values d; rw [←hcost]; omega
      · exact htie c (by omega)

theorem PaddingMap (values : List Int) (lower : Option Int) (lo hi best i d : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) :
    ∀ x ∈ values,
      (do return (← VeriPy.mod (d - (← VeriPy.mod x d)) d) : Except VeriPy.Error Int) =
        Except.ok ((d - x.fmod d).fmod d) := by
  have hb := (RangeCursor lo (hi+1) d pre suf hr).2
  have hlo := h.1.1
  intro x _
  exact ModPadding x d (by omega)

theorem MinimumChooseCursor (values : List Int) (lower : Option Int) (lo hi best i d candidate : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) (hiindex : i = Int.ofNat pre.length)
    (hcost : candidate = Padding values d)
    (choose : previous = none ∨ candidate < previous.getD 0 ∨ candidate = previous.getD 0 ∧ d > best) :
    _approximate_gcd__inv_33 values lower lo hi d (some candidate) (i+1) := by
  have hc := RangeCursor lo (hi+1) d pre suf hr
  apply MinimumChoose values lower lo hi best i d candidate previous h
  · rw [hiindex]; exact Int.natCast_nonneg _
  · rw [hiindex]; exact hc.1
  · omega
  · exact hcost
  · exact choose

theorem MinimumSkipCursor (values : List Int) (lower : Option Int) (lo hi best i d candidate : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) (hiindex : i = Int.ofNat pre.length)
    (hcost : candidate = Padding values d)
    (skip : ¬(previous = none ∨ candidate < previous.getD 0 ∨ candidate = previous.getD 0 ∧ d > best)) :
    _approximate_gcd__inv_33 values lower lo hi best previous (i+1) := by
  have hc := RangeCursor lo (hi+1) d pre suf hr
  apply MinimumSkip values lower lo hi best i d candidate previous h
  · rw [hiindex]; exact Int.natCast_nonneg _
  · rw [hiindex]; exact hc.1
  · exact hcost
  · exact skip

theorem MinimumPost (values : List Int) (lower : Option Int) (lo hi best i : Int)
    (previous : Option Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hne : values ≠ []) (hpos : ¬ ∃ x ∈ values, x ≤ 0)
    (hlo : lo = max 1 (if lower ≠ none then lower.getD 0 else 1))
    (hhi : hi = values.foldl max (values.headD 0)) (hend : lo+i = hi+1) :
    _approximate_gcd__post values lower best := by
  rcases h with ⟨bounds,initial,prior,price,minimum,tie⟩
  have hsome : previous ≠ none := by
    intro hn
    have hz := initial.mp hn
    omega
  have hprice := price.resolve_left (by exact fun hn => hn hsome)
  have hmin := minimum.resolve_left (by exact fun hn => hn hsome)
  have htie := tie.resolve_left (by exact fun hn => hn hsome)
  unfold _approximate_gcd__post
  change (False ↔ (Int.ofNat values.length = 0 ∨ ∃ x ∈ values, x ≤ 0)) ∧
    (¬¬False ∨ best ≥ max 1 (if lower ≠ none then lower.getD 0 else 1)) ∧ _
  rw [←hlo,←hhi]
  refine ⟨?_,Or.inr bounds.2.1,Or.inl (by omega),Or.inr bounds.2.2,Or.inr ?_,Or.inr ?_⟩
  · simp only [false_iff,not_or]
    constructor
    · intro hz; exact hne (List.length_eq_zero_iff.mp (Int.ofNat.inj hz))
    · exact hpos
  · intro c hc
    have hm := hmin c (by omega)
    rw [hprice] at hm
    exact hm
  · intro c hc
    have ht := htie c (by omega)
    rw [hprice] at ht
    exact ht

theorem MinimumEarly (values : List Int) (lower : Option Int) (lo hi : Int)
    (hne : values ≠ []) (hpos : ¬ ∃ x ∈ values, x ≤ 0)
    (hlo : lo = max 1 (if lower ≠ none then lower.getD 0 else 1))
    (hhi : hi = values.foldl max (values.headD 0)) (hearly : lo > hi) :
    _approximate_gcd__post values lower lo := by
  unfold _approximate_gcd__post
  rw [←hlo,←hhi]
  refine ⟨?_,Or.inr (Int.le_refl _),Or.inr rfl,Or.inl (by omega),Or.inr ?_,Or.inr ?_⟩
  · simp only [false_iff,not_or]
    constructor
    · intro hz; exact hne (List.length_eq_zero_iff.mp (Int.ofNat.inj hz))
    · exact hpos
  · intro c hc; omega
  · intro c hc; omega

theorem MinimumPostCursor (values : List Int) (lower : Option Int) (lo hi best i : Int)
    (previous : Option Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hne : values ≠ []) (hpos : ¬ ∃ x ∈ values, x ≤ 0)
    (hlo : lo = max 1 (if lower ≠ none then lower.getD 0 else 1))
    (hhi : hi = values.foldl max (values.headD 0))
    (hiindex : i = Int.ofNat (VeriPy.range lo (hi+1)).length) :
    _approximate_gcd__post values lower best := by
  apply MinimumPost values lower lo hi best i previous h hne hpos hlo hhi
  have bounds := h.1
  rw [RangeLength] at hiindex
  have he : Int.ofNat (hi+1-lo).toNat = hi+1-lo := Int.toNat_of_nonneg (by omega)
  rw [he] at hiindex
  omega

theorem MinimumChooseObserved (values result : List Int) (lower : Option Int) (lo hi best i d : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) (hiindex : i = Int.ofNat pre.length)
    (hresult : result = values.map (fun x => (d - x.fmod d).fmod d))
    (choose : previous = none ∨ result.sum < previous.getD 0 ∨ result.sum = previous.getD 0 ∧ d > best) :
    _approximate_gcd__inv_33 values lower lo hi d (some result.sum) (i+1) := by
  apply MinimumChooseCursor values lower lo hi best i d result.sum previous pre suf h hr hiindex
  · rw [hresult]; rfl
  · exact choose

theorem MinimumChooseNone (values result : List Int) (lower : Option Int) (lo hi best i d : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) (hiindex : i = Int.ofNat pre.length)
    (hresult : result = values.map (fun x => (d - x.fmod d).fmod d)) (hnone : previous = none) :
    _approximate_gcd__inv_33 values lower lo hi d (some result.sum) (i+1) := by
  exact MinimumChooseObserved values result lower lo hi best i d previous pre suf h hr hiindex hresult (Or.inl hnone)

theorem MinimumChooseLess (values result : List Int) (lower : Option Int) (lo hi best i d old : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) (hiindex : i = Int.ofNat pre.length)
    (hresult : result = values.map (fun x => (d - x.fmod d).fmod d))
    (hsome : previous = some old) (hless : result.sum < old) :
    _approximate_gcd__inv_33 values lower lo hi d (some result.sum) (i+1) := by
  apply MinimumChooseObserved values result lower lo hi best i d previous pre suf h hr hiindex hresult
  right; left; simpa [hsome] using hless

theorem MinimumChooseTie (values result : List Int) (lower : Option Int) (lo hi best i d old : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) (hiindex : i = Int.ofNat pre.length)
    (hresult : result = values.map (fun x => (d - x.fmod d).fmod d))
    (hsome : previous = some old) (htie : result.sum = old) (hlarger : d > best) :
    _approximate_gcd__inv_33 values lower lo hi d (some result.sum) (i+1) := by
  apply MinimumChooseObserved values result lower lo hi best i d previous pre suf h hr hiindex hresult
  right; right; exact ⟨by simpa [hsome] using htie,hlarger⟩

theorem MinimumSkipObserved (values result : List Int) (lower : Option Int) (lo hi best i d old : Int)
    (previous : Option Int) (pre suf : List Int)
    (h : _approximate_gcd__inv_33 values lower lo hi best previous i)
    (hr : VeriPy.range lo (hi+1) = pre ++ d :: suf) (hiindex : i = Int.ofNat pre.length)
    (hresult : result = values.map (fun x => (d - x.fmod d).fmod d))
    (hsome : previous = some old) (hless : ¬ result.sum < old)
    (htie : ¬ result.sum = old ∨ ¬ d > best) :
    _approximate_gcd__inv_33 values lower lo hi best (some old) (i+1) := by
  have hs : ¬ (previous = none ∨ result.sum < previous.getD 0 ∨ result.sum = previous.getD 0 ∧ d > best) := by
    simp only [hsome,reduceCtorEq,false_or,Option.getD_some]
    omega
  have hc : result.sum = Padding values d := by rw [hresult]; rfl
  have result := MinimumSkipCursor values lower lo hi best i d result.sum previous pre suf h hr hiindex hc hs
  simpa only [hsome] using result

@[spec]
theorem _approximate_gcd__proof («values» : (List Int)) («lower_bound» : (Option Int))  :
  ⦃⌜True⌝⦄ «_approximate_gcd» «values» «lower_bound» ⦃(fun __vp_result => ⌜(«_approximate_gcd__post» «values» «lower_bound» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_approximate_gcd__error» «values» «lower_bound» __vp_error)⌝, ())⦄ := by
  mvcgen [«_approximate_gcd», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 33; exact (by (first | veripy_capture «min_d» | veripy_let «min_d» := (max (1 : Int) (if ((«lower_bound» ≠ none)) then («lower_bound»).getD (0 : Int) else (1 : Int))) | veripy_capture_type «min_d» : Int); (first | veripy_capture «max_d» | veripy_let «max_d» := ((«values»).foldl max ((«values»).headD 0)) | veripy_capture_type «max_d» : Int); exact (fun ⟨__vp_cursor, «best_d», «best_pad», «__vp_index_33»⟩ => ⌜(«_approximate_gcd__inv_33» «values» «lower_bound» «min_d» «max_d» «best_d» «best_pad» «__vp_index_33») ∧ «__vp_index_33» = Int.ofNat __vp_cursor.prefix.length⌝, fun __vp_error => ⌜(«_approximate_gcd__error» «values» «lower_bound» __vp_error)⌝, ())))
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
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «MinimumChoose» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseLess» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseNone» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseObserved» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseTie» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumEarly» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumInit» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumPost» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumPostCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumSkip» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumSkipCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumSkipObserved» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ModPadding» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «Nonpositive» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PaddingMap» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeLength» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «MinimumChoose» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseLess» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseNone» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseObserved» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumChooseTie» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumEarly» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumInit» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumPost» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumPostCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumSkip» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumSkipCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «MinimumSkipObserved» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ModPadding» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «Nonpositive» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PaddingMap» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeCursor» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeLength» <;> first | assumption | rfl | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false] at *; first | assumption | rfl | omega) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«_approximate_gcd__post», «_approximate_gcd__error»] | grind (lax := true) [«MinimumChoose», «MinimumChooseCursor», «MinimumChooseLess», «MinimumChooseNone», «MinimumChooseObserved», «MinimumChooseTie», «MinimumEarly», «MinimumInit», «MinimumPost», «MinimumPostCursor», «MinimumSkip», «MinimumSkipCursor», «MinimumSkipObserved», «PaddingMap», «_approximate_gcd__inv_33», «_approximate_gcd__post», «_approximate_gcd__error»] | grind (lax := true) [«MinimumChoose», «MinimumChooseCursor», «MinimumChooseLess», «MinimumChooseNone», «MinimumChooseObserved», «MinimumChooseTie», «MinimumEarly», «MinimumInit», «MinimumPost», «MinimumPostCursor», «MinimumSkip», «MinimumSkipCursor», «MinimumSkipObserved», «ModPadding», «Nonpositive», «PaddingMap», «RangeCursor», «RangeLength», «_approximate_gcd__inv_33», «_approximate_gcd__post», «_approximate_gcd__error»]
  )
