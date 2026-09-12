-- Shared checked proof support; expanded into each standalone artifact.

theorem RangeCursor (n cur : Int) (pre suf : List Int)
    (h : VeriPy.range 0 n = pre ++ cur :: suf) :
    cur = Int.ofNat pre.length ∧ 0 ≤ cur ∧ cur < n := by
  have hl : pre.length < n.toNat := by
    have he := congrArg List.length h
    simp [VeriPy.range] at he
    omega
  have hr : (VeriPy.range 0 n).getD pre.length 0 = cur := by
    rw [h]; simp [List.getD_eq_getElem?_getD]
  have hv : (VeriPy.range 0 n).getD pre.length 0 = Int.ofNat pre.length := by
    simp [VeriPy.range, List.getD_eq_getElem?_getD, hl]
  rw [hv] at hr
  constructor
  · exact hr.symm
  constructor
  · rw [←hr]; exact Int.natCast_nonneg _
  · rw [←hr]
    exact Int.lt_of_toNat_lt (by simpa using hl)
