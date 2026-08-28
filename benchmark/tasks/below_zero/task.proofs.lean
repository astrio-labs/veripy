-- Slice-extension, the Dafny pack's twin. The Lean ladder happens to
-- close below_zero without it (the prelude's Take_succ_getD is within
-- the fixed scripts' reach), so under THIS prover the pack is
-- resolution-only: a `#@ proof` clause must name a declared lemma, and
-- this declares it, kernel-checked. The bounds ride as hypotheses —
-- the take-extension is FALSE unclamped — so the clause instantiation
-- lands it as a function in context: present, true, unused.

theorem SliceSnoc (s : List Int) (i : Int)
    (h0 : 0 ≤ i) (h1 : i < (s.length : Int)) :
    s.take ((i + 1)).toNat = s.take ((i)).toNat ++ [s.getD (i).toNat 0] := by
  have hn := VeriPy.Take_succ_getD s ((i)).toNat (by omega)
  rw [show (((i)).toNat + 1) = ((i + 1)).toNat from by omega] at hn
  exact hn
