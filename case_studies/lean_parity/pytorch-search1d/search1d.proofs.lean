-- VERIPY LIBRARY ranges
def At (xs : List Int) (i : Int) : Int :=
  xs.getD (if i < 0 then Int.ofNat xs.length+i else i).toNat default

abbrev Row := Int × Int × Int

def Lex (a b : Row) : Bool := decide (a.1 < b.1 ∨ a.1=b.1 ∧ (a.2.1 < b.2.1 ∨ a.2.1=b.2.1 ∧ a.2.2≤b.2.2))

def Rows (shards : List ShardMetadata) (dim : Int) : List Row :=
  (shards.zipIdx.map (fun (s,i) => (Int.ofNat i,s))).map (fun (i,s) =>
    (At s.shard_offsets dim,At s.shard_offsets dim+At s.shard_sizes dim-1,i))

def Domain (shards : List ShardMetadata) (dim : Int) : Prop :=
  ∀ j : Int, 0≤j ∧ j<Int.ofNat shards.length →
    (0≤dim ∧ dim<Int.ofNat (shards.getD j.toNat default).shard_offsets.length) ∧
    Int.ofNat (shards.getD j.toNat default).shard_sizes.length=Int.ofNat (shards.getD j.toNat default).shard_offsets.length ∧
    At (shards.getD j.toNat default).shard_sizes dim>0

theorem PermutedRows (rows : List Row) : (rows.mergeSort Lex).Perm rows := List.mergeSort_perm _ _

theorem LexTrans (a b c : Row) (hab : Lex a b) (hbc : Lex b c) : Lex a c := by
  simp only [Lex,decide_eq_true_eq] at *
  omega

theorem LexTotal (a b : Row) : Lex a b || Lex b a := by
  simp only [Lex,Bool.or_eq_true,decide_eq_true_eq]
  omega

theorem SortedStarts (rows : List Row) : (rows.mergeSort Lex).Pairwise (fun a b => a.1≤b.1) := by
  have h:=List.pairwise_mergeSort LexTrans LexTotal rows
  apply h.imp
  intro a b hab
  simp only [Lex,decide_eq_true_eq] at hab
  omega

theorem RowLength (shards : List ShardMetadata) (dim : Int) : (Rows shards dim).length=shards.length := by
  simp only [Rows,Row,List.length_map,List.length_zipIdx]

theorem RowAt (shards : List ShardMetadata) (dim : Int) (i : Nat) (hi : i<shards.length) :
    (Rows shards dim)[i]'(by rw [RowLength];exact hi) =
      (At shards[i].shard_offsets dim,At shards[i].shard_offsets dim+At shards[i].shard_sizes dim-1,Int.ofNat i) := by
  simp only [Rows,Row,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]

theorem RowIds (shards : List ShardMetadata) (dim : Int) :
    (Rows shards dim).map (fun r=>r.2.2) = (List.range shards.length).map Int.ofNat := by
  apply List.ext_getElem
  · simp [RowLength]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    rw [RowAt shards dim i (by simpa [RowLength] using hi)]

theorem RowIdsDistinct (shards : List ShardMetadata) (dim : Int) :
    ((Rows shards dim).mergeSort Lex).map (fun r=>r.2.2) |>.Nodup := by
  have hp:=(PermutedRows (Rows shards dim)).map (fun r=>r.2.2)
  apply hp.nodup_iff.mpr
  rw [RowIds]
  change List.Pairwise (fun x y : Int => x≠y) ((List.range shards.length).map Int.ofNat)
  rw [List.pairwise_map]
  exact List.Pairwise.imp (fun h he => h (Int.ofNat.inj he)) List.nodup_range

def RowFact (shards : List ShardMetadata) (dim : Int) (row : Row) : Prop :=
  (0≤row.2.2 ∧ row.2.2<Int.ofNat shards.length) ∧
  row.1=At (shards.getD row.2.2.toNat default).shard_offsets dim ∧
  row.2.1=row.1+At (shards.getD row.2.2.toNat default).shard_sizes dim-1 ∧ row.1≤row.2.1

theorem RowsMember (shards : List ShardMetadata) (dim : Int) (row : Row)
    (domain : Domain shards dim) (member : row ∈ Rows shards dim) : RowFact shards dim row := by
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp member
  have hb : i<shards.length := by simpa only [RowLength] using hi
  have hr:=RowAt shards dim i hb
  rw [hr] at he
  subst row
  have hc:=domain (Int.ofNat i) (by constructor; exact Int.natCast_nonneg _; exact Int.ofNat_lt.mpr hb)
  have read : shards.getD (Int.ofNat i).toNat default=shards[i] := by simp [List.getD_eq_getElem?_getD,hb]
  rw [read] at hc
  change (0≤Int.ofNat i ∧ Int.ofNat i<Int.ofNat shards.length) ∧ _
  refine ⟨⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hb⟩,?_,?_,?_⟩
  · rw [read]
  · rw [read]
  · change At shards[i].shard_offsets dim ≤ At shards[i].shard_offsets dim+At shards[i].shard_sizes dim-1
    have positive:=hc.2.2; omega

theorem SortedRowFact (shards : List ShardMetadata) (dim : Int) (row : Row)
    (domain : Domain shards dim) (member : row ∈ (Rows shards dim).mergeSort Lex) : RowFact shards dim row :=
  RowsMember shards dim row domain ((PermutedRows (Rows shards dim)).mem_iff.mp member)

theorem RowIncluded (shards : List ShardMetadata) (dim j : Int)
    (hj : 0≤j ∧ j<Int.ofNat shards.length) :
    (At (shards.getD j.toNat default).shard_offsets dim,
     At (shards.getD j.toNat default).shard_offsets dim+At (shards.getD j.toNat default).shard_sizes dim-1,j) ∈ Rows shards dim := by
  have hn : j.toNat<shards.length := by change 0≤j ∧ j<(↑shards.length:Int) at hj; omega
  have he : Int.ofNat j.toNat=j := Int.toNat_of_nonneg hj.1
  have read : shards.getD j.toNat default=shards[j.toNat] := by simp [List.getD_eq_getElem?_getD,hn]
  have hm := List.getElem_mem (l := Rows shards dim) (n := j.toNat) (by rw [RowLength];exact hn)
  rw [RowAt shards dim j.toNat hn] at hm
  simpa only [read,he] using hm

theorem BuildRow (shards : List ShardMetadata) (dim : Int) (item : Int × ShardMetadata)
    (domain : Domain shards dim)
    (member : item ∈ shards.zipIdx.map (fun (s,i)=>(Int.ofNat i,s))) :
    (do return (← VeriPy.getPython item.2.shard_offsets dim,
      (← VeriPy.getPython item.2.shard_offsets dim)+(← VeriPy.getPython item.2.shard_sizes dim)-1,item.1) : Except VeriPy.Error Row) =
      Except.ok (At item.2.shard_offsets dim,At item.2.shard_offsets dim+At item.2.shard_sizes dim-1,item.1) := by
  obtain ⟨⟨s,i⟩,hi,he⟩:=List.mem_map.mp member
  subst item
  have get:=List.mk_mem_zipIdx_iff_getElem?.mp hi
  obtain ⟨hb,hget⟩:=List.getElem?_eq_some_iff.mp get
  have read : shards.getD (Int.ofNat i).toNat default=s := by simp [List.getD_eq_getElem?_getD,get]
  have hc:=domain (Int.ofNat i) ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hb⟩
  rw [read] at hc
  have hdim : ¬dim<0 := by have := hc.1.1; omega
  have ho : 0≤dim ∧ dim< s.shard_offsets.length := hc.1
  have hz : 0≤dim ∧ dim< s.shard_sizes.length := by change 0≤dim ∧ dim<Int.ofNat s.shard_sizes.length; have := hc.1; have := hc.2.1; omega
  simp only [VeriPy.getPython,if_neg hdim,VeriPy.get,if_pos ho,if_pos hz,At]
  try simp only [if_neg hdim]
  rfl

theorem NoAdjacentOverlap (rows : List Row)
    (ordered : rows.Pairwise (fun a b=>a.1≤b.1))
    (adjacent : ∀ i : Nat, (h : i+1<rows.length) → rows[i].2.1<rows[i+1].1) :
    rows.Pairwise (fun a b=>a.2.1<b.1) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hn : i+1<rows.length := by omega
  have ha:=adjacent i hn
  by_cases he : i+1=j
  · simpa only [he] using ha
  · have hb:=List.pairwise_iff_getElem.mp ordered (i+1) j hn hj (by omega)
    omega

theorem PermutedDisjoint (rows : List Row) (a b : Row)
    (disjoint : rows.Pairwise (fun a b=>a.2.1<b.1))
    (ha : a∈rows) (hb : b∈rows) (hne : a.2.2≠b.2.2) : a.2.1<b.1 ∨ b.2.1<a.1 := by
  obtain ⟨i,hi,hei⟩:=List.mem_iff_getElem.mp ha
  obtain ⟨j,hj,hej⟩:=List.mem_iff_getElem.mp hb
  have hn : i≠j := by intro he; subst j; have hr:a=b:=hei.symm.trans hej; exact hne (congrArg (fun r=>r.2.2) hr)
  by_cases hlt : i<j
  · left; have h:=List.pairwise_iff_getElem.mp disjoint i j hi hj hlt; simpa only [hei,hej] using h
  · right; have h:=List.pairwise_iff_getElem.mp disjoint j i hj hi (by omega); simpa only [hei,hej] using h

theorem ShardDisjoint (shards : List ShardMetadata) (dim : Int)
    (disjoint : ((Rows shards dim).mergeSort Lex).Pairwise (fun a b=>a.2.1<b.1)) :
    _find_1d_overlapping_shards__post shards dim none := by
  refine ⟨Or.inl (by simp),Or.inl (by simp),Or.inr ?_⟩
  intro a ha b hb
  by_cases he : a=b
  · exact Or.inl he
  · have hma:=RowIncluded shards dim a ha
    have hmb:=RowIncluded shards dim b hb
    have hs:=PermutedRows (Rows shards dim)
    have h:=PermutedDisjoint _ _ _ disjoint (hs.mem_iff.mpr hma) (hs.mem_iff.mpr hmb) he
    right
    change At (shards.getD a.toNat default).shard_offsets dim+At (shards.getD a.toNat default).shard_sizes dim ≤ At (shards.getD b.toNat default).shard_offsets dim ∨
      At (shards.getD b.toNat default).shard_offsets dim+At (shards.getD b.toNat default).shard_sizes dim ≤ At (shards.getD a.toNat default).shard_offsets dim
    dsimp only at h
    omega

theorem FoundOverlap (shards : List ShardMetadata) (dim : Int) (i : Nat)
    (domain : Domain shards dim)
    (hi : i+1<((Rows shards dim).mergeSort Lex).length)
    (overlap : (((Rows shards dim).mergeSort Lex)[i]).2.1 ≥ (((Rows shards dim).mergeSort Lex)[i+1]).1) :
    _find_1d_overlapping_shards__post shards dim
      (some ((((Rows shards dim).mergeSort Lex)[i]).2.2, (((Rows shards dim).mergeSort Lex)[i+1]).2.2)) := by
  let rows := (Rows shards dim).mergeSort Lex
  have hi0 : i<rows.length := by dsimp [rows]; omega
  have hi1 : i+1<rows.length := hi
  have fa := SortedRowFact shards dim rows[i] domain (List.getElem_mem hi0)
  have fb := SortedRowFact shards dim rows[i+1] domain (List.getElem_mem hi1)
  have order := List.pairwise_iff_getElem.mp (SortedStarts (Rows shards dim)) i (i+1) hi0 hi1 (by omega)
  have distinct : rows[i].2.2 ≠ rows[i+1].2.2 := by
    have hn := RowIdsDistinct shards dim
    change List.Pairwise (fun a b : Int => a≠b) _ at hn
    rw [List.pairwise_map] at hn
    exact List.pairwise_iff_getElem.mp hn i (i+1) hi0 hi1 (by omega)
  obtain ⟨ha,ha0,ha1,ha2⟩ := fa
  obtain ⟨hb,hb0,hb1,hb2⟩ := fb
  have na : ¬rows[i].2.2<0 := by omega
  have nb : ¬rows[i+1].2.2<0 := by omega
  change _find_1d_overlapping_shards__post shards dim (some (rows[i].2.2,rows[i+1].2.2))
  simp only [_find_1d_overlapping_shards__post,Option.getD_some,reduceCtorEq,not_false_eq_true,not_true_eq_false,false_or,true_or,and_true,if_neg na,if_neg nb]
  simp only [ne_eq,reduceCtorEq,not_false_eq_true,not_true_eq_false,false_or]
  refine ⟨⟨ha,hb,distinct⟩,?_,?_⟩
  · change At (shards.getD rows[i].2.2.toNat default).shard_offsets dim < At (shards.getD rows[i+1].2.2.toNat default).shard_offsets dim+At (shards.getD rows[i+1].2.2.toNat default).shard_sizes dim
    dsimp only [rows] at *
    omega
  · change At (shards.getD rows[i+1].2.2.toNat default).shard_offsets dim < At (shards.getD rows[i].2.2.toNat default).shard_offsets dim+At (shards.getD rows[i].2.2.toNat default).shard_sizes dim
    dsimp only [rows] at *
    omega

theorem SearchInit (shards : List ShardMetadata) (dim : Int) (rows : List Row) :
    _find_1d_overlapping_shards__inv_22 shards dim rows 0 := by
  intro j hj; omega

theorem SearchStep (shards : List ShardMetadata) (dim i : Int) (rows : List Row)
    (inv : _find_1d_overlapping_shards__inv_22 shards dim rows i)
    (hi : 0≤i)
    (pair : (rows.getD i.toNat default).2.1 < (rows.getD (i+1).toNat default).1) :
    _find_1d_overlapping_shards__inv_22 shards dim rows (i+1) := by
  intro j hj
  by_cases he : j=i
  · subst j
    simpa only [if_neg (show ¬i+1<0 by omega)] using pair
  · exact inv j (by omega)

theorem SearchDone (shards : List ShardMetadata) (dim : Int)
    (inv : _find_1d_overlapping_shards__inv_22 shards dim ((Rows shards dim).mergeSort Lex) (Int.ofNat (Int.ofNat shards.length-1).toNat)) :
    _find_1d_overlapping_shards__post shards dim none := by
  apply ShardDisjoint
  apply NoAdjacentOverlap _ (SortedStarts _)
  intro i hi
  have len : ((Rows shards dim).mergeSort Lex).length=shards.length := by simp [RowLength]
  have hj : 0≤(Int.ofNat i) ∧ Int.ofNat i < 0+Int.ofNat (Int.ofNat shards.length-1).toNat := by
    rw [len] at hi
    simp only [VeriPy.ofNat_cast]
    omega
  have h:=inv (Int.ofNat i) hj
  have hn : ¬Int.ofNat i+1<0 := by omega
  have h0 : i<((Rows shards dim).mergeSort Lex).length := by omega
  have hn0 : (Int.ofNat i).toNat=i := rfl
  have hn1 : (Int.ofNat i+1).toNat=i+1 := by change ((i:Int)+1).toNat=i+1; omega
  simpa only [if_neg hn,hn0,hn1,
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem hi,Option.getD_some] using h



theorem BuildRows (shards : List ShardMetadata) (dim : Int)
    (domain : ∀ j : Int, 0≤j → j<Int.ofNat shards.length →
    (0≤dim ∧ dim<Int.ofNat (shards.getD j.toNat default).shard_offsets.length) ∧
    Int.ofNat (shards.getD j.toNat default).shard_sizes.length=Int.ofNat (shards.getD j.toNat default).shard_offsets.length ∧
    At (shards.getD j.toNat default).shard_sizes dim>0) :
    ∀ item ∈ shards.zipIdx.map (fun (s,i)=>(Int.ofNat i,s)),
    (do return (← VeriPy.getPython item.2.shard_offsets dim,
      (← VeriPy.getPython item.2.shard_offsets dim)+(← VeriPy.getPython item.2.shard_sizes dim)-1,item.1) : Except VeriPy.Error Row) =
      Except.ok (At item.2.shard_offsets dim,At item.2.shard_offsets dim+At item.2.shard_sizes dim-1,item.1) := by
  intro item member
  exact BuildRow shards dim item (fun j hj => domain j hj.1 hj.2) member

theorem SearchSafety (shards : List ShardMetadata) (dim cur : Int) (rows : List Row) (pre suf : List Int)
    (hr : rows=Rows shards dim)
    (hc : VeriPy.range 0 (Int.ofNat shards.length-1)=pre++cur::suf) :
    (0≤cur ∧ cur<Int.ofNat (rows.mergeSort Lex).length) ∧
    (0≤(if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1) ∧
    (if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1)<Int.ofNat (rows.mergeSort Lex).length) := by
  have h:=RangeCursor _ _ _ _ hc
  rw [hr]
  simp only [List.length_mergeSort,RowLength]
  rw [if_neg (show ¬cur+1<0 by omega)]
  omega

theorem SearchInvalidFirst (shards : List ShardMetadata) (dim cur : Int) (rows : List Row) (pre suf : List Int)
    (hr : rows=Rows shards dim)
    (hc : VeriPy.range 0 (Int.ofNat shards.length-1)=pre++cur::suf)
    (bad : ¬(0≤cur ∧ cur<Int.ofNat (rows.mergeSort Lex).length)) : False :=
  bad (SearchSafety shards dim cur rows pre suf hr hc).1

theorem SearchInvalidNext (shards : List ShardMetadata) (dim cur : Int) (rows : List Row) (pre suf : List Int)
    (hr : rows=Rows shards dim)
    (hc : VeriPy.range 0 (Int.ofNat shards.length-1)=pre++cur::suf)
    (bad : ¬(0≤(if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1) ∧
    (if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1)<Int.ofNat (rows.mergeSort Lex).length)) : False :=
  bad (SearchSafety shards dim cur rows pre suf hr hc).2

theorem SearchStepCursor (shards : List ShardMetadata) (dim cur i : Int) (rows : List Row) (pre suf : List Int)
    (hc : VeriPy.range 0 (Int.ofNat shards.length-1)=pre++cur::suf)
    (hi : i=Int.ofNat pre.length)
    (inv : _find_1d_overlapping_shards__inv_22 shards dim (rows.mergeSort Lex) i)
    (pair : ¬(rows.mergeSort Lex |>.getD cur.toNat default).2.1 ≥
       (rows.mergeSort Lex |>.getD (if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1).toNat default).1) :
    _find_1d_overlapping_shards__inv_22 shards dim (rows.mergeSort Lex) (i+1) := by
  have h:=RangeCursor _ _ _ _ hc
  have he : i=cur := hi.trans h.1.symm
  rw [he] at inv ⊢
  apply SearchStep _ _ _ _ inv h.2.1
  rw [if_neg (show ¬cur+1<0 by omega)] at pair
  omega

theorem SearchFoundCursor (shards : List ShardMetadata) (dim cur : Int) (rows : List Row) (pre suf : List Int)
    (domain : Domain shards dim) (hr : rows=Rows shards dim)
    (hc : VeriPy.range 0 (Int.ofNat shards.length-1)=pre++cur::suf)
    (pair : (rows.mergeSort Lex |>.getD cur.toNat default).2.1 ≥
       (rows.mergeSort Lex |>.getD (if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1).toNat default).1) :
    ∃ a, some ((rows.mergeSort Lex |>.getD cur.toNat default).2.2,
      (rows.mergeSort Lex |>.getD (if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1).toNat default).2.2)=a ∧
      _find_1d_overlapping_shards__post shards dim a := by
  subst rows
  have h:=RangeCursor _ _ _ _ hc
  have h0 : cur.toNat<((Rows shards dim).mergeSort Lex).length := by simp only [List.length_mergeSort,RowLength]; change cur.toNat<shards.length; have := h.2; simp only [VeriPy.ofNat_cast] at this; omega
  have h1 : cur.toNat+1<((Rows shards dim).mergeSort Lex).length := by simp only [List.length_mergeSort,RowLength]; have := h.2; simp only [VeriPy.ofNat_cast] at this; omega
  have hn : ¬cur+1<0 := by omega
  have he : (cur+1).toNat=cur.toNat+1 := by omega
  simp only [if_neg hn,he,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1,Option.getD_some] at pair ⊢
  exact ⟨_,rfl,FoundOverlap shards dim cur.toNat domain h1 pair⟩

theorem SearchReturn (shards : List ShardMetadata) (dim : Int) (rows : List Row)
    (r : Option (Option (Int × Int)) × Int) (a : Option (Int × Int))
    (h : r.1=none ∧ _find_1d_overlapping_shards__inv_22 shards dim (rows.mergeSort Lex) r.2 ∧ r.2=Int.ofNat (VeriPy.range 0 (Int.ofNat shards.length-1)).length ∨
      ∃ a, r.1=some a ∧ _find_1d_overlapping_shards__post shards dim a)
    (returned : r.1=some a) : _find_1d_overlapping_shards__post shards dim a := by
  rcases h with h | ⟨b,hb,post⟩
  · rw [returned] at h; simp at h
  · have he : a=b := Option.some.inj (returned.symm.trans hb); simpa only [he] using post

theorem SearchFinish (shards : List ShardMetadata) (dim : Int) (rows : List Row)
    (r : Option (Option (Int × Int)) × Int) (hr : rows=Rows shards dim)
    (h : r.1=none ∧ _find_1d_overlapping_shards__inv_22 shards dim (rows.mergeSort Lex) r.2 ∧ r.2=Int.ofNat (VeriPy.range 0 (Int.ofNat shards.length-1)).length ∨
      ∃ a, r.1=some a ∧ _find_1d_overlapping_shards__post shards dim a)
    (returned : r.1=none) : _find_1d_overlapping_shards__post shards dim none := by
  rcases h with ⟨_,inv,hi⟩ | ⟨a,ha,_⟩
  · subst rows
    rw [hi] at inv
    apply SearchDone
    simpa only [VeriPy.range,Int.sub_zero,List.length_map,List.length_range] using inv
  · rw [returned] at ha; contradiction
