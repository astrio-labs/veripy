-- General list facts connecting the original indexed comprehension to one loop step.
theorem FlattenStep (a : List (List α)) (b : List α) :
    (a ++ [b]).flatten = a.flatten ++ b := by simp

theorem RangeStep (i : Int) (hi : 0 ≤ i) :
    VeriPy.range 0 (i+1) = VeriPy.range 0 i ++ [i] := by
  have h : (i+1).toNat = i.toNat+1 := by omega
  simp [VeriPy.range, h, List.range_succ, show (i.toNat : Int) = i by omega]

theorem NormalizeInit (lines : List (Int × Int)) (src : List Nat) (count : Int) :
    sanitized_lines__inv_18 lines src [] count 0 := by
  simp [sanitized_lines__inv_18, VeriPy.range]

theorem NormalizeStep (lines pre suf : List (Int × Int)) (src : List Nat)
    (r : Int × Int) (good : List (Int × Int)) (count i : Int)
    (hl : lines = pre ++ r :: suf) (hi : i = Int.ofNat pre.length)
    (h : sanitized_lines__inv_18 lines src good count i) :
    sanitized_lines__inv_18 lines src
      (good ++ (if r.1 ≤ count ∧ r.2 ≥ max r.1 1 then [(max r.1 1, min r.2 count)] else [])) count (i+1) := by
  have hr : lines.getD i.toNat default = r := by simp [hl,hi,List.getD_eq_getElem?_getD]
  unfold sanitized_lines__inv_18 at *
  rw [RangeStep i (by simp [hi]), List.filter_append, List.map_append, ←h]
  simp only [List.filter_cons, hr]
  split <;> simp_all

theorem NormalizeSkipHigh (lines pre suf : List (Int × Int)) (src : List Nat)
    (r : Int × Int) (good : List (Int × Int)) (count i : Int)
    (hl : lines = pre ++ r :: suf) (hi : i = Int.ofNat pre.length)
    (h : sanitized_lines__inv_18 lines src good count i) (bad : r.1 > count) :
    sanitized_lines__inv_18 lines src good count (i+1) := by
  have hs := NormalizeStep lines pre suf src r good count i hl hi h
  simpa [show ¬ r.1 ≤ count by omega] using hs

theorem NormalizeSkipLow (lines pre suf : List (Int × Int)) (src : List Nat)
    (r : Int × Int) (good : List (Int × Int)) (count i : Int)
    (hl : lines = pre ++ r :: suf) (hi : i = Int.ofNat pre.length)
    (h : sanitized_lines__inv_18 lines src good count i) (bad : r.2 < max r.1 1) :
    sanitized_lines__inv_18 lines src good count (i+1) := by
  have hs := NormalizeStep lines pre suf src r good count i hl hi h
  simpa [show ¬ r.2 ≥ max r.1 1 by omega] using hs

theorem NormalizeKeep (lines pre suf : List (Int × Int)) (src : List Nat)
    (r : Int × Int) (good : List (Int × Int)) (count i : Int)
    (hl : lines = pre ++ r :: suf) (hi : i = Int.ofNat pre.length)
    (h : sanitized_lines__inv_18 lines src good count i)
    (start : ¬ r.1 > count) (finish : ¬ r.2 < max r.1 1) :
    sanitized_lines__inv_18 lines src (good ++ [(max r.1 1, min r.2 count)]) count (i+1) := by
  have hs := NormalizeStep lines pre suf src r good count i hl hi h
  simpa [show r.1 ≤ count by omega, show r.2 ≥ max r.1 1 by omega] using hs

theorem NormalizePost (lines : List (Int × Int)) (src : List Nat)
    (good : List (Int × Int)) (count : Int) (hne : src ≠ [])
    (hc : count = Int.ofNat (src.count (10 : Nat)) + (if [10].isSuffixOf src then 0 else 1))
    (h : sanitized_lines__inv_18 lines src good count (Int.ofNat lines.length)) :
    sanitized_lines__post lines src good := by
  have hl : Int.ofNat src.length ≠ (0 : Int) := by
    intro hz
    have hn : src.length = 0 := Int.ofNat.inj hz
    exact hne (List.length_eq_zero_iff.mp hn)
  unfold sanitized_lines__post
  rw [if_neg hl]
  unfold sanitized_lines__inv_18 at h
  rw [hc] at h
  exact h
