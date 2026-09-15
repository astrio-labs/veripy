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
def LuhnCompleted (s a digit : List Nat) : Prop :=
  digit.length = 1 ∧ (∀ c ∈ digit.map (fun c => [c]), c.isInfixOf_internal a = true) ∧ LuhnExact (s ++ digit) a 0
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

@[spec]
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

theorem LuhnHead (v : List Int) (d : Int) :
    LuhnTotal (d::v) 10 = d + LuhnTotal (0::v) 10 := by
  cases v <;> simp [LuhnTotal, Int.add_assoc]

theorem CheckDigitComplete (s a : List Nat) (ck : Int)
    (ha : a = [48,49,50,51,52,53,54,55,56,57])
    (hk : 0 ≤ ck ∧ ck < 10)
    (hc : LuhnExact (s ++ [a.getD 0 0]) a ck) :
    LuhnCompleted s a [a.getD (if -ck < 0 then Int.ofNat a.length + -ck else -ck).toNat 0] := by
  subst a
  have cases : ck=0 ∨ ck=1 ∨ ck=2 ∨ ck=3 ∨ ck=4 ∨ ck=5 ∨ ck=6 ∨ ck=7 ∨ ck=8 ∨ ck=9 := by omega
  have he (d : Nat) : LuhnDigits (s ++ [d]) [48,49,50,51,52,53,54,55,56,57] =
      VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [d] :: LuhnDigits s [48,49,50,51,52,53,54,55,56,57] := by
    simp [LuhnDigits, List.reverse_append]
  change ck = (LuhnTotal (LuhnDigits (s ++ [48]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10 at hc
  rw [he] at hc
  have hz : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [48] = 0 := rfl
  rw [hz] at hc
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [48]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [48]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [48] = 0 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [57]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [57]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [57] = 9 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [56]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [56]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [56] = 8 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [55]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [55]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [55] = 7 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [54]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [54]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [54] = 6 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [53]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [53]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [53] = 5 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [52]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [52]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [52] = 4 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [51]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [51]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [51] = 3 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [50]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [50]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [50] = 2 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega
  · change LuhnCompleted s [48,49,50,51,52,53,54,55,56,57] [49]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hmem
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst c
      decide
    · change 0 = (LuhnTotal (LuhnDigits (s ++ [49]) [48,49,50,51,52,53,54,55,56,57]) 10).fmod 10
      rw [he]
      have hd : VeriPy.stringFind [48,49,50,51,52,53,54,55,56,57] [49] = 1 := rfl
      rw [hd, LuhnHead]
      rw [Int.fmod_eq_emod] at hc ⊢
      try simp only [show ¬ (10 : Int) < 0 from by decide, if_false] at hc ⊢
      omega

@[spec]
theorem calc_check_digit__proof (number alphabet : List Nat)
    (ha : alphabet = [48,49,50,51,52,53,54,55,56,57])
    (hn : ∀ c ∈ number.map (fun c => [c]), c.isInfixOf_internal alphabet = true) :
    ⦃⌜True⌝⦄ calc_check_digit number alphabet
      ⦃(fun r => ⌜calc_check_digit__post number alphabet r⌝,
        fun e => ⌜calc_check_digit__error number alphabet e⌝, ())⦄ := by
  mvcgen [calc_check_digit, VeriPy.getPython, VeriPy.get]
  case vc2.hn =>
    intro c hc
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl
    · exact hn c hc
    · subst alphabet; decide
  case vc3.isTrue.success.isTrue =>
    rename_i hb ck hp hi
    have hc := CheckDigitComplete number alphabet ck ha hp.1 hp.2
    unfold calc_check_digit__post
    constructor
    · simp
    · exact ⟨hc.2.1, hc⟩
  case vc4.isTrue.success.isFalse =>
    rename_i hb ck hp hi
    have bounds := hp.1
    subst alphabet
    have hi' : ¬ ((0 ≤ if -ck < 0 then 10 + -ck else -ck) ∧ (if -ck < 0 then 10 + -ck else -ck) < 10) := hi
    split at hi' <;> omega
  case vc5.isFalse =>
    subst alphabet
    simp at *

theorem check_digit_roundtrip__proof (number alphabet : List Nat)
    (ha : alphabet = [48,49,50,51,52,53,54,55,56,57])
    (hn : ∀ c ∈ number.map (fun c => [c]), c.isInfixOf_internal alphabet = true) :
    ⦃⌜True⌝⦄ check_digit_roundtrip number alphabet
      ⦃(fun r => ⌜check_digit_roundtrip__post number alphabet r⌝,
        fun e => ⌜check_digit_roundtrip__error number alphabet e⌝, ())⦄ := by
  mvcgen [check_digit_roundtrip]
  all_goals simp_all [calc_check_digit__post, checksum__post, LuhnCompleted, LuhnExact, check_digit_roundtrip__post, List.map_append, List.mem_append]
  all_goals grind
