-- The Dafny pack's twin. Under Lean the domination post closes by the
-- prelude's GetD_le_ListMax_take (prefix membership + foldl-max
-- dominance), so this pack is resolution-only: a `#@ proof` clause
-- must name a declared lemma, and this declares it, kernel-checked.
-- The nonemptiness rides as a hypothesis — the OptionalMax template
-- invokes none of it, and the screen says so honestly.

theorem SeqMaxDominatesAll (s : List Int) : ∀ i : Int, ∀ j : Int,
    0 ≤ j → j ≤ i → i < (s.length : Int) →
    s.getD (j).toNat 0 ≤ VeriPy.ListMax (s.take ((i + 1)).toNat) := by
  intro i j h0 h1 h2
  exact VeriPy.GetD_le_ListMax_take s j i h0 h1 h2
