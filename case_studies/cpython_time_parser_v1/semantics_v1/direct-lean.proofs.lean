theorem _is_ascii_digit__proof (c : List Nat) :
  ⦃⌜True⌝⦄ «_is_ascii_digit» c
    ⦃(fun r => ⌜«_is_ascii_digit__post» c r⌝,
      fun e => ⌜«_is_ascii_digit__error» c e⌝, ())⦄ := by
  mvcgen [«_is_ascii_digit»]
  simp_all [«_is_ascii_digit__post», «_is_ascii_digit__error»]


@[simp] theorem ParserEmptyDecimal : VeriPy.tryDecimal [] = none := by rfl


theorem ParserSliceSingleton (xs : List Nat) (i : Int) (h : 0 ≤ i) (hb : i < xs.length) :
    VeriPy.slice xs i (i+1) = [xs.getD i.toNat 0] := by
  have hi : i.toNat < xs.length := by omega
  have hw : (i+1).toNat - i.toNat = 1 := by omega
  simp only [VeriPy.slice, if_neg (by omega : ¬ i < 0), if_neg (by omega : ¬ i+1 < 0), List.drop_take, hw]
  simp [List.take_one, List.getD_eq_getElem?_getD, hi]

theorem ParserSliceClamped (xs : List Nat) (lo hi : Int) (hl : 0 ≤ lo) (hh : (xs.length : Int) ≤ hi) :
    VeriPy.slice xs lo hi = xs.drop lo.toNat := by
  have hn : xs.length ≤ hi.toNat := by omega
  simp [VeriPy.slice, if_neg (by omega : ¬ lo < 0), if_neg (by omega : ¬ hi < 0), List.take_of_length_le hn]

theorem ParserSlicePastEnd (xs : List Nat) (lo hi : Int) (h : (xs.length : Int) ≤ lo) :
    VeriPy.slice xs lo hi = [] := by
  have hnonneg : ¬ lo < 0 := by omega
  simp only [VeriPy.slice, if_neg hnonneg]
  apply List.drop_of_length_le
  have bound := List.length_take_le' (if hi < 0 then max 0 ((xs.length : Int) + hi) else hi).toNat xs
  omega



@[simp] theorem ParserWPError {α : Type} (e : VeriPy.Error)
    (Q : PostCond α (.except VeriPy.Error .pure)) :
    wp⟦(Except.error e : Except VeriPy.Error α)⟧ Q = Q.2.1 e := rfl


@[simp] theorem ParserBindError {α β : Type} (e : VeriPy.Error) (f : α → Except VeriPy.Error β) :
    ((Except.error e : Except VeriPy.Error α) >>= f) = Except.error e := rfl
@[simp] theorem ParserMapError {α β : Type} (e : VeriPy.Error) (f : α → β) :
    (f <$> (Except.error e : Except VeriPy.Error α)) = Except.error e := rfl
theorem ParserLength0Sep (tstr : List Nat) (hlen : tstr.length = 0)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 := ParserSlicePastEnd tstr 2 3 (by omega)
  simp_all

theorem ParserLength0Compact (tstr : List Nat) (hlen : tstr.length = 0)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 := ParserSlicePastEnd tstr 2 3 (by omega)
  have hs4 := ParserSlicePastEnd tstr 4 5 (by omega)
  have hs6 := ParserSlicePastEnd tstr 6 7 (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 0 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 0 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 0 (by omega)
  have hes := ParserSlicePastEnd tstr 0 0 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength1Sep (tstr : List Nat) (hlen : tstr.length = 1)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 := ParserSlicePastEnd tstr 2 3 (by omega)
  simp_all

theorem ParserLength1Compact (tstr : List Nat) (hlen : tstr.length = 1)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 := ParserSlicePastEnd tstr 2 3 (by omega)
  have hs4 := ParserSlicePastEnd tstr 4 5 (by omega)
  have hs6 := ParserSlicePastEnd tstr 6 7 (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 1 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 1 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 1 (by omega)
  have hes := ParserSlicePastEnd tstr 1 1 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength2Sep (tstr : List Nat) (hlen : tstr.length = 2)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 := ParserSlicePastEnd tstr 2 3 (by omega)
  simp_all

theorem ParserLength2Compact (tstr : List Nat) (hlen : tstr.length = 2)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 := ParserSlicePastEnd tstr 2 3 (by omega)
  have hs4 := ParserSlicePastEnd tstr 4 5 (by omega)
  have hs6 := ParserSlicePastEnd tstr 6 7 (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 2 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 2 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 2 (by omega)
  have hes := ParserSlicePastEnd tstr 2 2 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength3Sep (tstr : List Nat) (hlen : tstr.length = 3)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSlicePastEnd tstr 5 6 (by omega)
  have hs8 := ParserSlicePastEnd tstr 8 9 (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 3 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 3 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 3 (by omega)
  have hes := ParserSlicePastEnd tstr 3 3 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength3Compact (tstr : List Nat) (hlen : tstr.length = 3)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 := ParserSlicePastEnd tstr 4 5 (by omega)
  have hs6 := ParserSlicePastEnd tstr 6 7 (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 3 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 3 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 3 (by omega)
  have hes := ParserSlicePastEnd tstr 3 3 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength4Sep (tstr : List Nat) (hlen : tstr.length = 4)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSlicePastEnd tstr 5 6 (by omega)
  have hs8 := ParserSlicePastEnd tstr 8 9 (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 4 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 4 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 4 (by omega)
  have hes := ParserSlicePastEnd tstr 4 4 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength4Compact (tstr : List Nat) (hlen : tstr.length = 4)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 := ParserSlicePastEnd tstr 4 5 (by omega)
  have hs6 := ParserSlicePastEnd tstr 6 7 (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 4 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 4 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 4 (by omega)
  have hes := ParserSlicePastEnd tstr 4 4 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength5Sep (tstr : List Nat) (hlen : tstr.length = 5)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSlicePastEnd tstr 5 6 (by omega)
  have hs8 := ParserSlicePastEnd tstr 8 9 (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 5 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 5 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 5 (by omega)
  have hes := ParserSlicePastEnd tstr 5 5 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength5Compact (tstr : List Nat) (hlen : tstr.length = 5)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSlicePastEnd tstr 6 7 (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 5 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 5 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 5 (by omega)
  have hes := ParserSlicePastEnd tstr 5 5 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength6Sep (tstr : List Nat) (hlen : tstr.length = 6)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSlicePastEnd tstr 8 9 (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 6 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 6 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 6 (by omega)
  have hes := ParserSlicePastEnd tstr 6 6 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength6Compact (tstr : List Nat) (hlen : tstr.length = 6)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSlicePastEnd tstr 6 7 (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 6 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 6 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 6 (by omega)
  have hes := ParserSlicePastEnd tstr 6 6 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength7Sep (tstr : List Nat) (hlen : tstr.length = 7)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSlicePastEnd tstr 8 9 (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 7 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 7 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 7 (by omega)
  have hes := ParserSlicePastEnd tstr 7 7 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength7Compact (tstr : List Nat) (hlen : tstr.length = 7)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 7 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 7 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 7 (by omega)
  have hes := ParserSlicePastEnd tstr 7 7 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 7)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength8Sep (tstr : List Nat) (hlen : tstr.length = 8)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSlicePastEnd tstr 8 9 (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 8 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 8 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 8 (by omega)
  have hes := ParserSlicePastEnd tstr 8 8 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength8Compact (tstr : List Nat) (hlen : tstr.length = 8)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 8 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 8 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 8 (by omega)
  have hes := ParserSlicePastEnd tstr 8 8 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 8)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength9Sep (tstr : List Nat) (hlen : tstr.length = 9)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 9 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 9 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 9 (by omega)
  have hes := ParserSlicePastEnd tstr 9 9 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 9)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength9Compact (tstr : List Nat) (hlen : tstr.length = 9)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 9 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 9 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 9 (by omega)
  have hes := ParserSlicePastEnd tstr 9 9 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 9)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength10Sep (tstr : List Nat) (hlen : tstr.length = 10)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 10 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 10 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 10 (by omega)
  have hes := ParserSlicePastEnd tstr 10 10 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 10)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength10Compact (tstr : List Nat) (hlen : tstr.length = 10)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 10 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 10 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 10 (by omega)
  have hes := ParserSlicePastEnd tstr 10 10 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 10)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength11Sep (tstr : List Nat) (hlen : tstr.length = 11)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 11 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 11 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 11 (by omega)
  have hes := ParserSlicePastEnd tstr 11 11 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 11)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength11Compact (tstr : List Nat) (hlen : tstr.length = 11)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 11 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 11 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 11 (by omega)
  have hes := ParserSlicePastEnd tstr 11 11 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 11)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength12Sep (tstr : List Nat) (hlen : tstr.length = 12)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 12 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 12 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 12 (by omega)
  have hes := ParserSlicePastEnd tstr 12 12 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 12)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength12Compact (tstr : List Nat) (hlen : tstr.length = 12)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 12 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 12 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 12 (by omega)
  have hes := ParserSlicePastEnd tstr 12 12 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 12)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength13Sep (tstr : List Nat) (hlen : tstr.length = 13)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 13 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 13 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 13 (by omega)
  have hes := ParserSlicePastEnd tstr 13 13 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 13)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength13Compact (tstr : List Nat) (hlen : tstr.length = 13)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  have hc : VeriPy.slice tstr 7 13 = VeriPy.slice tstr 7 13 := by
    simp only [ParserSliceClamped tstr 7 13 (by omega) (by omega), ParserSliceClamped tstr 7 13 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 13 13 (by omega)
  have hes := ParserSlicePastEnd tstr 13 13 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 13)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength14Sep (tstr : List Nat) (hlen : tstr.length = 14)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 14 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 14 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 14 (by omega)
  have hes := ParserSlicePastEnd tstr 14 14 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 14)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength14Compact (tstr : List Nat) (hlen : tstr.length = 14)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 13)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength15Sep (tstr : List Nat) (hlen : tstr.length = 15)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  have hc : VeriPy.slice tstr 9 15 = VeriPy.slice tstr 9 15 := by
    simp only [ParserSliceClamped tstr 9 15 (by omega) (by omega), ParserSliceClamped tstr 9 15 (by omega) (by omega)]
  have he := ParserSlicePastEnd tstr 15 15 (by omega)
  have hes := ParserSlicePastEnd tstr 15 15 (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 15)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength15Compact (tstr : List Nat) (hlen : tstr.length = 15)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 13)
  all_goals simp_all only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp_all [«_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength16Sep (tstr : List Nat) (hlen : 16 ≤ tstr.length)
    (hsep : VeriPy.slice tstr 2 3 = [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hb0 : (0 : Int) < (tstr.length : Int) := by omega
  have hb1 : (1 : Int) < (tstr.length : Int) := by omega
  have hb2 : (2 : Int) < (tstr.length : Int) := by omega
  have hb3 : (3 : Int) < (tstr.length : Int) := by omega
  have hb4 : (4 : Int) < (tstr.length : Int) := by omega
  have hb5 : (5 : Int) < (tstr.length : Int) := by omega
  have hb6 : (6 : Int) < (tstr.length : Int) := by omega
  have hb7 : (7 : Int) < (tstr.length : Int) := by omega
  have hb8 : (8 : Int) < (tstr.length : Int) := by omega
  have hb9 : (9 : Int) < (tstr.length : Int) := by omega
  have hb10 : (10 : Int) < (tstr.length : Int) := by omega
  have hb11 : (11 : Int) < (tstr.length : Int) := by omega
  have hb12 : (12 : Int) < (tstr.length : Int) := by omega
  have hb13 : (13 : Int) < (tstr.length : Int) := by omega
  have hb14 : (14 : Int) < (tstr.length : Int) := by omega
  have hb15 : (15 : Int) < (tstr.length : Int) := by omega
  have hb16 : (16 : Int) ≤ (tstr.length : Int) := by omega
  have hr7 : (6 : Int) ≤ (tstr.length : Int) - 7 := by omega
  have hr9 : (6 : Int) ≤ (tstr.length : Int) - 9 := by omega
  have hneg00 : ¬ ((tstr.length : Int) < 0) := by omega
  have hneg01 : ¬ ((tstr.length : Int) ≤ 0) := by omega
  have hneg02 : ¬ ((tstr.length : Int) = 0) := by omega
  have hneg10 : ¬ ((tstr.length : Int) < 1) := by omega
  have hneg11 : ¬ ((tstr.length : Int) ≤ 1) := by omega
  have hneg12 : ¬ ((tstr.length : Int) = 1) := by omega
  have hneg20 : ¬ ((tstr.length : Int) < 2) := by omega
  have hneg21 : ¬ ((tstr.length : Int) ≤ 2) := by omega
  have hneg22 : ¬ ((tstr.length : Int) = 2) := by omega
  have hneg30 : ¬ ((tstr.length : Int) < 3) := by omega
  have hneg31 : ¬ ((tstr.length : Int) ≤ 3) := by omega
  have hneg32 : ¬ ((tstr.length : Int) = 3) := by omega
  have hneg40 : ¬ ((tstr.length : Int) < 4) := by omega
  have hneg41 : ¬ ((tstr.length : Int) ≤ 4) := by omega
  have hneg42 : ¬ ((tstr.length : Int) = 4) := by omega
  have hneg50 : ¬ ((tstr.length : Int) < 5) := by omega
  have hneg51 : ¬ ((tstr.length : Int) ≤ 5) := by omega
  have hneg52 : ¬ ((tstr.length : Int) = 5) := by omega
  have hneg60 : ¬ ((tstr.length : Int) < 6) := by omega
  have hneg61 : ¬ ((tstr.length : Int) ≤ 6) := by omega
  have hneg62 : ¬ ((tstr.length : Int) = 6) := by omega
  have hneg70 : ¬ ((tstr.length : Int) < 7) := by omega
  have hneg71 : ¬ ((tstr.length : Int) ≤ 7) := by omega
  have hneg72 : ¬ ((tstr.length : Int) = 7) := by omega
  have hneg80 : ¬ ((tstr.length : Int) < 8) := by omega
  have hneg81 : ¬ ((tstr.length : Int) ≤ 8) := by omega
  have hneg82 : ¬ ((tstr.length : Int) = 8) := by omega
  have hneg90 : ¬ ((tstr.length : Int) < 9) := by omega
  have hneg91 : ¬ ((tstr.length : Int) ≤ 9) := by omega
  have hneg92 : ¬ ((tstr.length : Int) = 9) := by omega
  have hneg100 : ¬ ((tstr.length : Int) < 10) := by omega
  have hneg101 : ¬ ((tstr.length : Int) ≤ 10) := by omega
  have hneg102 : ¬ ((tstr.length : Int) = 10) := by omega
  have hneg110 : ¬ ((tstr.length : Int) < 11) := by omega
  have hneg111 : ¬ ((tstr.length : Int) ≤ 11) := by omega
  have hneg112 : ¬ ((tstr.length : Int) = 11) := by omega
  have hneg120 : ¬ ((tstr.length : Int) < 12) := by omega
  have hneg121 : ¬ ((tstr.length : Int) ≤ 12) := by omega
  have hneg122 : ¬ ((tstr.length : Int) = 12) := by omega
  have hneg130 : ¬ ((tstr.length : Int) < 13) := by omega
  have hneg131 : ¬ ((tstr.length : Int) ≤ 13) := by omega
  have hneg132 : ¬ ((tstr.length : Int) = 13) := by omega
  have hneg140 : ¬ ((tstr.length : Int) < 14) := by omega
  have hneg141 : ¬ ((tstr.length : Int) ≤ 14) := by omega
  have hneg142 : ¬ ((tstr.length : Int) = 14) := by omega
  have hneg150 : ¬ ((tstr.length : Int) < 15) := by omega
  have hneg151 : ¬ ((tstr.length : Int) ≤ 15) := by omega
  have hneg152 : ¬ ((tstr.length : Int) = 15) := by omega
  have hrneg02 : ¬ ((tstr.length : Int) - 0 < 2) := by omega
  have hrneg06 : ¬ ((tstr.length : Int) - 0 < 6) := by omega
  have hrneg22 : ¬ ((tstr.length : Int) - 2 < 2) := by omega
  have hrneg26 : ¬ ((tstr.length : Int) - 2 < 6) := by omega
  have hrneg32 : ¬ ((tstr.length : Int) - 3 < 2) := by omega
  have hrneg36 : ¬ ((tstr.length : Int) - 3 < 6) := by omega
  have hrneg42 : ¬ ((tstr.length : Int) - 4 < 2) := by omega
  have hrneg46 : ¬ ((tstr.length : Int) - 4 < 6) := by omega
  have hrneg62 : ¬ ((tstr.length : Int) - 6 < 2) := by omega
  have hrneg66 : ¬ ((tstr.length : Int) - 6 < 6) := by omega
  have hrneg72 : ¬ ((tstr.length : Int) - 7 < 2) := by omega
  have hrneg76 : ¬ ((tstr.length : Int) - 7 < 6) := by omega
  have hrneg92 : ¬ ((tstr.length : Int) - 9 < 2) := by omega
  have hrneg96 : ¬ ((tstr.length : Int) - 9 < 6) := by omega
  have hs5 := ParserSliceSingleton tstr 5 (by omega) (by omega)
  have hs8 := ParserSliceSingleton tstr 8 (by omega) (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 3 5) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 6 8) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 9 15)
  all_goals by_cases hc5 : VeriPy.slice tstr 5 6 = [58]
  all_goals by_cases hf : (VeriPy.slice tstr 8 9).isInfixOf_internal [46,44] = true
  all_goals by_cases htail : (((VeriPy.slice tstr 15 tstr.length).map (fun c => [c])).all (fun c => decide (c.isInfixOf_internal [48,49,50,51,52,53,54,55,56,57] = true))) = true
  all_goals simp only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp [*, «_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem ParserLength16Compact (tstr : List Nat) (hlen : 16 ≤ tstr.length)
    (hsep : VeriPy.slice tstr 2 3 ≠ [58]) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hb0 : (0 : Int) < (tstr.length : Int) := by omega
  have hb1 : (1 : Int) < (tstr.length : Int) := by omega
  have hb2 : (2 : Int) < (tstr.length : Int) := by omega
  have hb3 : (3 : Int) < (tstr.length : Int) := by omega
  have hb4 : (4 : Int) < (tstr.length : Int) := by omega
  have hb5 : (5 : Int) < (tstr.length : Int) := by omega
  have hb6 : (6 : Int) < (tstr.length : Int) := by omega
  have hb7 : (7 : Int) < (tstr.length : Int) := by omega
  have hb8 : (8 : Int) < (tstr.length : Int) := by omega
  have hb9 : (9 : Int) < (tstr.length : Int) := by omega
  have hb10 : (10 : Int) < (tstr.length : Int) := by omega
  have hb11 : (11 : Int) < (tstr.length : Int) := by omega
  have hb12 : (12 : Int) < (tstr.length : Int) := by omega
  have hb13 : (13 : Int) < (tstr.length : Int) := by omega
  have hb14 : (14 : Int) < (tstr.length : Int) := by omega
  have hb15 : (15 : Int) < (tstr.length : Int) := by omega
  have hb16 : (16 : Int) ≤ (tstr.length : Int) := by omega
  have hr7 : (6 : Int) ≤ (tstr.length : Int) - 7 := by omega
  have hr9 : (6 : Int) ≤ (tstr.length : Int) - 9 := by omega
  have hneg00 : ¬ ((tstr.length : Int) < 0) := by omega
  have hneg01 : ¬ ((tstr.length : Int) ≤ 0) := by omega
  have hneg02 : ¬ ((tstr.length : Int) = 0) := by omega
  have hneg10 : ¬ ((tstr.length : Int) < 1) := by omega
  have hneg11 : ¬ ((tstr.length : Int) ≤ 1) := by omega
  have hneg12 : ¬ ((tstr.length : Int) = 1) := by omega
  have hneg20 : ¬ ((tstr.length : Int) < 2) := by omega
  have hneg21 : ¬ ((tstr.length : Int) ≤ 2) := by omega
  have hneg22 : ¬ ((tstr.length : Int) = 2) := by omega
  have hneg30 : ¬ ((tstr.length : Int) < 3) := by omega
  have hneg31 : ¬ ((tstr.length : Int) ≤ 3) := by omega
  have hneg32 : ¬ ((tstr.length : Int) = 3) := by omega
  have hneg40 : ¬ ((tstr.length : Int) < 4) := by omega
  have hneg41 : ¬ ((tstr.length : Int) ≤ 4) := by omega
  have hneg42 : ¬ ((tstr.length : Int) = 4) := by omega
  have hneg50 : ¬ ((tstr.length : Int) < 5) := by omega
  have hneg51 : ¬ ((tstr.length : Int) ≤ 5) := by omega
  have hneg52 : ¬ ((tstr.length : Int) = 5) := by omega
  have hneg60 : ¬ ((tstr.length : Int) < 6) := by omega
  have hneg61 : ¬ ((tstr.length : Int) ≤ 6) := by omega
  have hneg62 : ¬ ((tstr.length : Int) = 6) := by omega
  have hneg70 : ¬ ((tstr.length : Int) < 7) := by omega
  have hneg71 : ¬ ((tstr.length : Int) ≤ 7) := by omega
  have hneg72 : ¬ ((tstr.length : Int) = 7) := by omega
  have hneg80 : ¬ ((tstr.length : Int) < 8) := by omega
  have hneg81 : ¬ ((tstr.length : Int) ≤ 8) := by omega
  have hneg82 : ¬ ((tstr.length : Int) = 8) := by omega
  have hneg90 : ¬ ((tstr.length : Int) < 9) := by omega
  have hneg91 : ¬ ((tstr.length : Int) ≤ 9) := by omega
  have hneg92 : ¬ ((tstr.length : Int) = 9) := by omega
  have hneg100 : ¬ ((tstr.length : Int) < 10) := by omega
  have hneg101 : ¬ ((tstr.length : Int) ≤ 10) := by omega
  have hneg102 : ¬ ((tstr.length : Int) = 10) := by omega
  have hneg110 : ¬ ((tstr.length : Int) < 11) := by omega
  have hneg111 : ¬ ((tstr.length : Int) ≤ 11) := by omega
  have hneg112 : ¬ ((tstr.length : Int) = 11) := by omega
  have hneg120 : ¬ ((tstr.length : Int) < 12) := by omega
  have hneg121 : ¬ ((tstr.length : Int) ≤ 12) := by omega
  have hneg122 : ¬ ((tstr.length : Int) = 12) := by omega
  have hneg130 : ¬ ((tstr.length : Int) < 13) := by omega
  have hneg131 : ¬ ((tstr.length : Int) ≤ 13) := by omega
  have hneg132 : ¬ ((tstr.length : Int) = 13) := by omega
  have hneg140 : ¬ ((tstr.length : Int) < 14) := by omega
  have hneg141 : ¬ ((tstr.length : Int) ≤ 14) := by omega
  have hneg142 : ¬ ((tstr.length : Int) = 14) := by omega
  have hneg150 : ¬ ((tstr.length : Int) < 15) := by omega
  have hneg151 : ¬ ((tstr.length : Int) ≤ 15) := by omega
  have hneg152 : ¬ ((tstr.length : Int) = 15) := by omega
  have hrneg02 : ¬ ((tstr.length : Int) - 0 < 2) := by omega
  have hrneg06 : ¬ ((tstr.length : Int) - 0 < 6) := by omega
  have hrneg22 : ¬ ((tstr.length : Int) - 2 < 2) := by omega
  have hrneg26 : ¬ ((tstr.length : Int) - 2 < 6) := by omega
  have hrneg32 : ¬ ((tstr.length : Int) - 3 < 2) := by omega
  have hrneg36 : ¬ ((tstr.length : Int) - 3 < 6) := by omega
  have hrneg42 : ¬ ((tstr.length : Int) - 4 < 2) := by omega
  have hrneg46 : ¬ ((tstr.length : Int) - 4 < 6) := by omega
  have hrneg62 : ¬ ((tstr.length : Int) - 6 < 2) := by omega
  have hrneg66 : ¬ ((tstr.length : Int) - 6 < 6) := by omega
  have hrneg72 : ¬ ((tstr.length : Int) - 7 < 2) := by omega
  have hrneg76 : ¬ ((tstr.length : Int) - 7 < 6) := by omega
  have hrneg92 : ¬ ((tstr.length : Int) - 9 < 2) := by omega
  have hrneg96 : ¬ ((tstr.length : Int) - 9 < 6) := by omega
  have hs2 : VeriPy.slice tstr 2 3 ≠ [] := by
    have hx : VeriPy.slice tstr 2 3 = [tstr.getD 2 0] := by
      simpa using ParserSliceSingleton tstr 2 (by omega) (by omega)
    simp [hx]
  have hs4 : VeriPy.slice tstr 4 5 ≠ [] := by
    have hx : VeriPy.slice tstr 4 5 = [tstr.getD 4 0] := by
      simpa using ParserSliceSingleton tstr 4 (by omega) (by omega)
    simp [hx]
  have hs6 := ParserSliceSingleton tstr 6 (by omega) (by omega)
  cases hd0 : VeriPy.tryDecimal (VeriPy.slice tstr 0 2) <;>
    cases hd1 : VeriPy.tryDecimal (VeriPy.slice tstr 2 4) <;>
    cases hd2 : VeriPy.tryDecimal (VeriPy.slice tstr 4 6) <;>
    cases hd3 : VeriPy.tryDecimal (VeriPy.slice tstr 7 13)
  all_goals by_cases hf : (VeriPy.slice tstr 6 7).isInfixOf_internal [46,44] = true
  all_goals by_cases htail : (((VeriPy.slice tstr 13 tstr.length).map (fun c => [c])).all (fun c => decide (c.isInfixOf_internal [48,49,50,51,52,53,54,55,56,57] = true))) = true
  all_goals simp only [«_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error»]
  all_goals simp [*, «_parse_hh_mm_ss_ff», VeriPy.decimal, VeriPy.set, VeriPy.setPython,
      VeriPy.getPython, VeriPy.get, VeriPy.raise, Triple.iff,
      «_parse_hh_mm_ss_ff__post», «_parse_hh_mm_ss_ff__error», MonadExceptOf.throw,
      List.all_eq_true]
  all_goals repeat' first | (exfalso; omega) | simp_all [MonadExceptOf.throw, List.all_eq_true] | split

theorem _parse_hh_mm_ss_ff__proof (tstr : List Nat) :
    ⦃⌜True⌝⦄ «_parse_hh_mm_ss_ff» tstr
      ⦃(fun r => ⌜«_parse_hh_mm_ss_ff__post» tstr r⌝,
        fun e => ⌜«_parse_hh_mm_ss_ff__error» tstr e⌝, ())⦄ := by
  have hcases : tstr.length = 0 ∨ tstr.length = 1 ∨ tstr.length = 2 ∨ tstr.length = 3 ∨ tstr.length = 4 ∨ tstr.length = 5 ∨ tstr.length = 6 ∨ tstr.length = 7 ∨ tstr.length = 8 ∨ tstr.length = 9 ∨ tstr.length = 10 ∨ tstr.length = 11 ∨ tstr.length = 12 ∨ tstr.length = 13 ∨ tstr.length = 14 ∨ tstr.length = 15 ∨ 16 ≤ tstr.length := by omega
  rcases hcases with hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen | hlen
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength0Sep tstr hlen hs
    · exact ParserLength0Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength1Sep tstr hlen hs
    · exact ParserLength1Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength2Sep tstr hlen hs
    · exact ParserLength2Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength3Sep tstr hlen hs
    · exact ParserLength3Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength4Sep tstr hlen hs
    · exact ParserLength4Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength5Sep tstr hlen hs
    · exact ParserLength5Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength6Sep tstr hlen hs
    · exact ParserLength6Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength7Sep tstr hlen hs
    · exact ParserLength7Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength8Sep tstr hlen hs
    · exact ParserLength8Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength9Sep tstr hlen hs
    · exact ParserLength9Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength10Sep tstr hlen hs
    · exact ParserLength10Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength11Sep tstr hlen hs
    · exact ParserLength11Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength12Sep tstr hlen hs
    · exact ParserLength12Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength13Sep tstr hlen hs
    · exact ParserLength13Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength14Sep tstr hlen hs
    · exact ParserLength14Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength15Sep tstr hlen hs
    · exact ParserLength15Compact tstr hlen hs
  · by_cases hs : VeriPy.slice tstr 2 3 = [58]
    · exact ParserLength16Sep tstr hlen hs
    · exact ParserLength16Compact tstr hlen hs
