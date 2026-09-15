def Base36Alphabet : List Nat := [48,49,50,51,52,53,54,55,56,57,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122]

def Digits (n : Int) : List Nat :=
  if n < 36 then [Base36Alphabet.getD n.toNat 0]
  else Digits (n.fdiv 36) ++ [Base36Alphabet.getD (n.fmod 36).toNat 0]
termination_by n.toNat
decreasing_by
  simp only [Int.fdiv_eq_ediv_of_nonneg n (show (0 : Int) ≤ 36 by decide)]
  omega

def EncodingProgress (original remaining : Int) (suffix : List Nat) : Prop :=
  original ≥ 0 ∧ remaining ≥ 0 ∧
    Digits original = (if remaining = 0 then suffix else Digits remaining ++ suffix)
-- VERIPY PRELUDE END

theorem SmallEncoding (n : Int) (chars : List Nat) (hn : 0 ≤ n ∧ n < 36)
    (hc : chars = Base36Alphabet) : [chars.getD n.toNat 0] = Digits n := by
  rw [Digits]
  simp [hc, show n < 36 by omega]

theorem EncodingComplete (original : Int) (output : List Nat)
    (h : EncodingProgress original 0 output) : output = Digits original := by
  simpa [EncodingProgress] using h.2.2.symm


theorem EncodingStep (original remaining : Int) (suffix chars : List Nat)
    (hp : remaining > 0) (h : EncodingProgress original remaining suffix)
    (hc : chars = Base36Alphabet) :
    EncodingProgress original (remaining.fdiv 36) ([chars.getD (remaining.fmod 36).toNat 0] ++ suffix) := by
  have hd : remaining.fdiv 36 = remaining / 36 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hm : remaining.fmod 36 = remaining % 36 := by rw [Int.fmod_eq_emod]; simp
  have hq : 0 ≤ remaining.fdiv 36 := by rw [hd]; omega
  rcases h with ⟨ho,hr,he⟩
  unfold EncodingProgress
  refine ⟨ho,hq,?_⟩
  rw [if_neg (show remaining ≠ 0 by omega)] at he
  rw [he, Digits]
  by_cases small : remaining < 36
  · have hz : remaining.fdiv 36 = 0 := by rw [hd]; omega
    have hrem : remaining.fmod 36 = remaining := by rw [hm]; omega
    simp [small,hz,hrem,hc]
  · have hn : remaining.fdiv 36 ≠ 0 := by rw [hd]; omega
    simp [small,hn,hc,List.append_assoc]

theorem Base36Init (original : Int) (chars : List Nat) (h : ¬ original < 36) :
    int_to_base36__inv_12 original original chars [] := by
  unfold int_to_base36__inv_12 EncodingProgress
  simp [show original ≠ 0 by omega]
  omega

theorem Base36Finish (original remaining : Int) (chars output : List Nat)
    (h : int_to_base36__inv_12 original remaining chars output) (done : ¬ remaining ≠ 0) :
    int_to_base36__post original output := by
  rcases h with ⟨hi,hlen,hprogress⟩
  have ho := hprogress.1
  unfold int_to_base36__post
  simp only [false_iff, not_false_eq_true, not_true_eq_false, false_or]
  constructor <;> omega

theorem Base36SmallBounds (chars : List Nat) (i : Int) (hc : chars = Base36Alphabet)
    (hi : ¬ i < 0) (hb : i < 36)
    (bad : ¬ (0 ≤ (if i < 0 then Int.ofNat chars.length + i else i) ∧
      (if i < 0 then Int.ofNat chars.length + i else i) < Int.ofNat chars.length)) : False := by
  simp [hc,Base36Alphabet,hi] at bad
  omega

theorem Base36Remainder (i : Int) : 0 ≤ i.fmod 36 ∧ i.fmod 36 < 36 := by
  have he : i.fmod 36 = i % 36 := by rw [Int.fmod_eq_emod]; simp
  rw [he]
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem Base36Step (original remaining : Int) (chars suffix : List Nat)
    (h : int_to_base36__inv_12 original remaining chars suffix)
    (hne : remaining ≠ 0) (hc : chars = Base36Alphabet) :
    int_to_base36__inv_12 original (remaining.fdiv 36) chars
      ([chars.getD (if remaining.fmod 36 < 0 then Int.ofNat chars.length + remaining.fmod 36 else remaining.fmod 36).toNat 0] ++ suffix) := by
  have hb := Base36Remainder remaining
  rw [if_neg (show ¬ remaining.fmod 36 < 0 by omega)]
  rcases h with ⟨hi,hlen,hg⟩
  refine ⟨?_, ?_, EncodingStep original remaining suffix chars (by omega) hg hc⟩
  · rw [Int.fdiv_eq_ediv_of_nonneg remaining (show (0 : Int) ≤ 36 by decide)]
    omega
  · left; simp

theorem Base36Decrease (original remaining : Int) (chars suffix : List Nat) (measure : Nat)
    (h : int_to_base36__inv_12 original remaining chars suffix)
    (hne : remaining ≠ 0) (hm : remaining.toNat = measure) :
    (remaining.fdiv 36).toNat < measure := by
  have hi := h.1
  rw [←hm, Int.fdiv_eq_ediv_of_nonneg remaining (show (0 : Int) ≤ 36 by decide)]
  omega

theorem Base36ModBounds (chars : List Nat) (remaining : Int) (hc : chars = Base36Alphabet)
    (bad : ¬ (0 ≤ (if remaining.fmod 36 < 0 then Int.ofNat chars.length + remaining.fmod 36 else remaining.fmod 36) ∧
      (if remaining.fmod 36 < 0 then Int.ofNat chars.length + remaining.fmod 36 else remaining.fmod 36) < Int.ofNat chars.length)) : False := by
  have h := Base36Remainder remaining
  exact Base36SmallBounds chars (remaining.fmod 36) hc (by omega) h.2 bad

theorem Base36ExactFinish (original remaining : Int) (chars output : List Nat)
    (h : int_to_base36__inv_12 original remaining chars output) (done : ¬ remaining ≠ 0) :
    output = Digits original := by
  have hz : remaining = 0 := by omega
  subst remaining
  exact EncodingComplete original output h.2.2

theorem Base36ExactSmall (i : Int) (chars : List Nat)
    (hi : ¬ i < 0) (hb : i < 36) (hc : chars = Base36Alphabet) :
    [chars.getD (if i < 0 then Int.ofNat chars.length + i else i).toNat 0] = Digits i := by
  rw [if_neg hi]
  exact SmallEncoding i chars ⟨by omega,hb⟩ hc

-- Exact-output certificate, matching the two audited Dafny return certificates.
theorem Base36Exact (i : Int) (hi : 0 ≤ i) :
  ⦃⌜True⌝⦄ int_to_base36 i ⦃(fun value => ⌜value = Digits i⌝, fun (_ : VeriPy.Error) => ⌜False⌝, ())⦄ := by
  mvcgen [«int_to_base36», VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (exact (by let «__vp_old_i» := «i»; veripy_capture «char_set»; exact fun («i», «b36») => ⟨(«i»).toNat⟩))
  all_goals try (exact (by let «__vp_old_i» := «i»; veripy_capture «char_set»; exact (fun __vp_state => match __vp_state with | .inl («i», «b36») => ⌜(«int_to_base36__inv_12» «__vp_old_i» «i» «char_set» «b36»)⌝ | .inr («i», «b36») => ⌜(«int_to_base36__inv_12» «__vp_old_i» «i» «char_set» «b36») ∧ ¬ ((«i» ≠ (0 : Int)))⌝, fun _ => ⌜False⌝, ())))
  all_goals (
    try (simp only [WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals first | (apply Base36ExactFinish <;> first | assumption | rfl | omega) | (apply Base36ExactSmall <;> first | assumption | rfl | omega) | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (apply «Base36Decrease» <;> first | assumption | rfl | omega) | (apply «Base36Finish» <;> first | assumption | rfl | omega) | (apply «Base36Init» <;> first | assumption | rfl | omega) | (apply «Base36ModBounds» <;> first | assumption | rfl | omega) | (apply «Base36Remainder» <;> first | assumption | rfl | omega) | (apply «Base36SmallBounds» <;> first | assumption | rfl | omega) | (apply «Base36Step» <;> first | assumption | rfl | omega) | (apply «EncodingComplete» <;> first | assumption | rfl | omega) | (apply «EncodingStep» <;> first | assumption | rfl | omega) | (apply «SmallEncoding» <;> first | assumption | rfl | omega) | (exfalso; first | (apply «Base36Decrease» <;> first | assumption | rfl | omega) | (apply «Base36Finish» <;> first | assumption | rfl | omega) | (apply «Base36Init» <;> first | assumption | rfl | omega) | (apply «Base36ModBounds» <;> first | assumption | rfl | omega) | (apply «Base36Remainder» <;> first | assumption | rfl | omega) | (apply «Base36SmallBounds» <;> first | assumption | rfl | omega) | (apply «Base36Step» <;> first | assumption | rfl | omega) | (apply «EncodingComplete» <;> first | assumption | rfl | omega) | (apply «EncodingStep» <;> first | assumption | rfl | omega) | (apply «SmallEncoding» <;> first | assumption | rfl | omega)) | grind [«int_to_base36__post»] | grind [«Base36Decrease», «Base36Finish», «Base36Init», «Base36ModBounds», «Base36Remainder», «Base36SmallBounds», «Base36Step», «EncodingComplete», «EncodingStep», «SmallEncoding», «int_to_base36__post»]
  )
#print axioms Base36Exact
