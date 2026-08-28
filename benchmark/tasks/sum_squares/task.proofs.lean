-- The Dafny pack's twin. Under Lean the `result >= 0` post closes by
-- the prelude's PySum_sq_nonneg (spelled for exactly the mapped-square
-- shape), so this pack is resolution-only: a `#@ proof` clause must
-- name a declared lemma, and this declares it, kernel-checked. The
-- nonnegativity hypothesis rides along — sum-nonnegativity is FALSE
-- for arbitrary lists — so the clause instantiation (which cannot
-- discharge side conditions, and skips list-valued arguments anyway)
-- leaves it present, true, unused.

theorem SumNonNeg (s : List Int) (h : ∀ x, x ∈ s → 0 ≤ x) :
    0 ≤ VeriPy.PySum s := by
  induction s with
  | nil => simp [VeriPy.PySum]
  | cons x xs ih =>
    simp only [VeriPy.PySum]
    have hx := h x (List.mem_cons_self)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega
