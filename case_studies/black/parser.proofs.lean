theorem ReadCursor [Inhabited α] (pre suf : List α) (value : α) :
    (pre ++ value :: suf).getD pre.length default = value := by
  simp [List.getD_eq_getElem?_getD]

theorem AppendReadBefore [Inhabited α] (xs : List α) (value : α) (j : Nat) (hj : j < xs.length) :
    (xs ++ [value]).getD j default = xs.getD j default := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hj]

theorem AppendReadAt [Inhabited α] (xs : List α) (value : α) :
    (xs ++ [value]).getD xs.length default = value := by
  simp [List.getD_eq_getElem?_getD]

theorem ParserInit (source : List (List Nat)) : parse_line_ranges__inv_6 source [] 0 := by
  unfold parse_line_ranges__inv_6
  simp
  constructor <;> intro j hj <;> omega

theorem ParserStep (source pre suf : List (List Nat)) (current : List Nat)
    (output : List (Int × Int)) (i first last : Int)
    (hs : source = pre ++ current :: suf) (hi : i = Int.ofNat pre.length)
    (h : parse_line_ranges__inv_6 source output i)
    (hparts : Int.ofNat (current.splitOn 45).length = 2)
    (hfirst : VeriPy.tryDecimal ((current.splitOn 45).getD 0 default) = some first)
    (hlast : VeriPy.tryDecimal ((current.splitOn 45).getD 1 default) = some last) :
    parse_line_ranges__inv_6 source (output ++ [(first,last)]) (i+1) := by
  rcases h with ⟨hlen,hvalid,hvalue⟩
  have hi0 : 0 ≤ i := by rw [hi]; exact Int.natCast_nonneg _
  have hout : output.length = i.toNat := by rw [←hlen]; rfl
  have hread : source.getD i.toNat default = current := by rw [hs,hi]; simpa using ReadCursor pre suf current
  refine ⟨by simp; omega, ?_, ?_⟩
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [hread]
      exact ⟨hparts, by change VeriPy.tryDecimal ((current.splitOn 45).getD 0 default) ≠ none; rw [hfirst]; simp, by change VeriPy.tryDecimal ((current.splitOn 45).getD 1 default) ≠ none; rw [hlast]; simp⟩
    · exact hvalid j (by omega)
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [←hout, AppendReadAt]
      rw [hout,hread]
      change (first,last) = ((VeriPy.tryDecimal ((current.splitOn 45).getD 0 default)).getD 0, (VeriPy.tryDecimal ((current.splitOn 45).getD 1 default)).getD 0)
      rw [hfirst,hlast]; rfl
    · rw [AppendReadBefore _ _ _ (by omega)]
      exact hvalue j (by omega)

theorem ParserPost (source : List (List Nat)) (output : List (Int × Int))
    (h : parse_line_ranges__inv_6 source output (Int.ofNat source.length)) :
    parse_line_ranges__post source output := by
  rcases h with ⟨hlen,hvalid,hvalue⟩
  unfold parse_line_ranges__post
  refine ⟨?_,Or.inr hlen,Or.inr hvalue⟩
  exact ⟨False.elim,fun hn => hn hvalid⟩


theorem ParserInvalid (source pre suf : List (List Nat)) (current : List Nat)
    (hs : source = pre ++ current :: suf)
    (bad : ¬ (Int.ofNat (current.splitOn 45).length = 2 ∧
      VeriPy.tryDecimal ((current.splitOn 45).getD 0 default) ≠ none ∧
      VeriPy.tryDecimal ((current.splitOn 45).getD 1 default) ≠ none)) :
    parse_line_ranges__error source VeriPy.Error.value := by
  unfold parse_line_ranges__error
  refine ⟨rfl,⟨fun _ hall => ?_,fun _ => trivial⟩,Or.inl (by simp),Or.inl (by simp)⟩
  have hb : 0 ≤ Int.ofNat pre.length ∧ Int.ofNat pre.length < Int.ofNat source.length := by
    rw [hs]; simp; omega
  have hc := hall (Int.ofNat pre.length) hb
  rw [hs] at hc
  have he : (Int.ofNat pre.length).toNat = pre.length := rfl
  rw [he,ReadCursor] at hc
  exact bad hc

theorem ParserBadLength (source pre suf : List (List Nat)) (current : List Nat)
    (hs : source = pre ++ current :: suf)
    (bad : Int.ofNat (current.splitOn 45).length ≠ 2) :
    parse_line_ranges__error source VeriPy.Error.value :=
  ParserInvalid source pre suf current hs (fun h => bad h.1)

theorem ParserBadFirst (source pre suf : List (List Nat)) (current : List Nat)
    (hs : source = pre ++ current :: suf)
    (bad : VeriPy.tryDecimal ((current.splitOn 45).getD 0 default) = none) :
    parse_line_ranges__error source VeriPy.Error.value :=
  ParserInvalid source pre suf current hs (fun h => h.2.1 bad)

theorem ParserBadLast (source pre suf : List (List Nat)) (current : List Nat)
    (hs : source = pre ++ current :: suf)
    (bad : VeriPy.tryDecimal ((current.splitOn 45).getD 1 default) = none) :
    parse_line_ranges__error source VeriPy.Error.value :=
  ParserInvalid source pre suf current hs (fun h => h.2.2 bad)
