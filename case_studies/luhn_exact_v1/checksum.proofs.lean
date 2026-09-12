def LuhnDouble (x n : Int) : Int := (2*x).fdiv n + (2*x).fmod n
def LuhnTotal (v : List Int) (n : Int) : Int :=
  match v with
  | [] => 0
  | [x] => x
  | x::y::tail => x + LuhnDouble y n + LuhnTotal tail n
def LuhnDigits (s a : List Nat) : List Int :=
  s.reverse.map (fun c => VeriPy.stringFind a [c])
def LuhnExact (s a : List Nat) (r : Int) : Prop :=
  r = (LuhnTotal (LuhnDigits s a) (Int.ofNat a.length)).fmod (Int.ofNat a.length)
-- VERIPY PRELUDE END

theorem LuhnBridge (v : List Int) (n : Int) :
    (VeriPy.takeEvery v 2).sum + ((VeriPy.takeEvery (v.drop 1) 2).map (fun x => LuhnDouble x n)).sum = LuhnTotal v n := by
  match v with
  | [] => simp [VeriPy.takeEvery, VeriPy.takeEveryAux, LuhnTotal]
  | [x] => simp [VeriPy.takeEvery, VeriPy.takeEveryAux, LuhnTotal]
  | x::y::tail =>
    have ih := LuhnBridge tail n
    have hs : VeriPy.takeEveryAux tail 2 1 = VeriPy.takeEveryAux (tail.drop 1) 2 0 := by
      cases tail <;> rfl
    simp only [VeriPy.takeEvery, VeriPy.takeEveryAux, List.drop_succ_cons, List.drop_zero, List.map_cons, List.sum_cons, LuhnTotal, show (2 : Nat)-1=1 from rfl] at *
    rw [hs]
    omega

theorem LuhnMapOk (xs : List α) (f : α → Except VeriPy.Error β) (model : α → β)
    (h : ∀ x ∈ xs, f x = Except.ok (model x)) :
    VeriPy.mapChecked f model xs = Except.ok (xs.map model) := by
  unfold VeriPy.mapChecked
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem LuhnIndexOk (c : Nat)
    (h : [c].isInfixOf_internal [48,49,50,51,52,53,54,55,56,57] = true) :
    VeriPy.stringIndex [48,49,50,51,52,53,54,55,56,57] [c] = Except.ok (VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [c]) := by
  have hc : c ∈ ([48,49,50,51,52,53,54,55,56,57] : List Nat) :=
    (List.isInfixOf_internal_iff_isInfix.mp h).mem (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem checksum__proof (number alphabet : List Nat)
    (ha : alphabet = [48,49,50,51,52,53,54,55,56,57])
    (hn : ∀ c ∈ number.map (fun c => [c]), c.isInfixOf_internal alphabet = true) :
    ⦃⌜True⌝⦄ checksum number alphabet
      ⦃(fun r => ⌜checksum__post number alphabet r⌝,
        fun e => ⌜checksum__error number alphabet e⌝, ())⦄ := by
  subst alphabet
  mvcgen [checksum, VeriPy.mod, VeriPy.divmod]
  case vc1.h =>
    intro i hi
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hi)
    exact LuhnIndexOk c (hn [c] (List.mem_map.mpr ⟨c,hc,rfl⟩))
  case vc2.h =>
    try dsimp (config := { zetaDelta := true }) only at *
    intro x hx
    rfl
  case vc3.success.success.isTrue =>
    rename_i n v hv w hz hw
    have impossible : (10 : Int) = 0 := hz
    omega
  case vc4.success.success.isFalse =>
    try dsimp (config := { zetaDelta := true }) only at *
    subst_vars
    simp only [checksum__post, LuhnExact, List.length_cons, List.length_nil, Nat.reduceAdd, Int.ofNat_eq_natCast]
    constructor
    · rw [Int.fmod_eq_emod]
      simp
      omega
    · simp only [VeriPy.stride, VeriPy.slice, Int.not_ofNat_neg, if_false, Int.toNat_natCast, List.take_length, List.drop_zero, Int.toNat_one]
      have hb := LuhnBridge (LuhnDigits number [48,49,50,51,52,53,54,55,56,57]) 10
      simp only [LuhnDigits, List.map_reverse, List.map_map, Function.comp_def, LuhnDouble, Int.mul_comm] at hb ⊢
      simpa [show ¬ (0 : Int) < 0 from by decide, show ¬ (1 : Int) < 0 from by decide, if_false, Int.toNat_zero, Int.toNat_one, List.drop_zero] using congrArg (fun x : Int => x.fmod 10) hb
