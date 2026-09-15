-- VERIPY PRELUDE END

theorem LuhnIndexMap (a : List Nat) (xs : List (List Nat)) :
    VeriPy.mapChecked (fun i => (do return (← VeriPy.stringIndex a i) : Except VeriPy.Error Int))
      (fun i => VeriPy.stringFind a i) xs =
    if (∀ i ∈ xs, 0 ≤ VeriPy.stringFind a i) then
      Except.ok (xs.map (fun i => VeriPy.stringFind a i)) else Except.error VeriPy.Error.value := by
  unfold VeriPy.mapChecked
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons]
    by_cases hx : 0 ≤ VeriPy.stringFind a x
    · have he : VeriPy.stringIndex a x = Except.ok (VeriPy.stringFind a x) := by
        unfold VeriPy.stringIndex
        rw [if_neg (by omega)]
        rfl
      simp only [he, bind_pure_comp, ih, List.mem_cons, forall_eq_or_imp, hx, true_and, List.map_cons]
      split <;> rfl
    · have he : VeriPy.stringIndex a x = Except.error VeriPy.Error.value := by
        unfold VeriPy.stringIndex
        rw [if_pos (by omega)]
        rfl
      simp only [he, List.mem_cons, forall_eq_or_imp, hx, false_and, if_false]
      rfl

@[spec]
theorem checksum__proof (number alphabet : List Nat) (ha : Int.ofNat alphabet.length > 1) :
    ⦃⌜True⌝⦄ checksum number alphabet
      ⦃(fun r => ⌜checksum__post number alphabet r⌝,
        fun e => ⌜checksum__error number alphabet e⌝, ())⦄ := by
  by_cases hn : ∀ i ∈ (number.map (fun c => [c])).reverse, 0 ≤ VeriPy.stringFind alphabet i
  · mvcgen [checksum, VeriPy.mod, VeriPy.divmod]
    all_goals try (intro i hi; unfold VeriPy.stringIndex; rw [if_neg (by have := hn i hi; omega)]; rfl)
    all_goals try (intro x hx; dsimp (config := { zetaDelta := true }) only; unfold VeriPy.divmod; rw [if_neg (by omega)]; rfl)
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals simp_all [checksum__post, checksum__error, Int.fmod_eq_emod, Int.emod_nonneg, Int.emod_lt_of_pos]
    all_goals try exact Int.emod_lt_of_pos _ (by omega)
    all_goals try (
      intro x hx
      have hne : alphabet ≠ [] := by intro he; subst alphabet; simp at ha
      rw [if_neg hne]
      rfl)
    all_goals omega
  · have he := LuhnIndexMap alphabet ((number.map (fun c => [c])).reverse)
    rw [if_neg hn] at he
    have hbad : checksum number alphabet = Except.error VeriPy.Error.value := by
      simp only [checksum, he]
      rfl
    rw [hbad]
    change ⦃⌜True⌝⦄ (VeriPy.raise VeriPy.Error.value : Except VeriPy.Error Int) ⦃_⦄
    mvcgen
    simpa [checksum__error, List.mem_reverse] using hn

@[spec]
theorem validate__proof (number alphabet : List Nat) (ha : Int.ofNat alphabet.length > 1) :
    ⦃⌜True⌝⦄ validate number alphabet
      ⦃(fun r => ⌜validate__post number alphabet r⌝,
        fun e => ⌜validate__error number alphabet e⌝, ())⦄ := by
  mvcgen [validate]
  all_goals simp_all [checksum__post, checksum__error, validate__post, validate__error]
  all_goals try omega
  all_goals grind [List.length_eq_zero_iff]
