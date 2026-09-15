-- VERIPY LIBRARY ranges
def Read [Inhabited α] (xs : List α) (i : Int) : α := xs.getD (if i<0 then Int.ofNat xs.length+i else i).toNat default

def ShardsOverlap (a b : ShardMetadata) : Prop :=
  a.shard_offsets.length=a.shard_sizes.length ∧ b.shard_offsets.length=b.shard_sizes.length ∧ a.shard_offsets.length=b.shard_offsets.length ∧
  ∀ d : Int, 0≤d ∧ d<Int.ofNat a.shard_offsets.length →
    Read a.shard_offsets d < Read b.shard_offsets d+Read b.shard_sizes d ∧
    Read b.shard_offsets d < Read a.shard_offsets d+Read a.shard_sizes d

def Start (shards : List ShardMetadata) (d i : Int) : Int := Read (Read shards i).shard_offsets d

def End (shards : List ShardMetadata) (d i : Int) : Int := Start shards d i+Read (Read shards i).shard_sizes d

def SweepDomain (shards : List ShardMetadata) (order : List Int) (d : Int) : Prop :=
  shards≠[] ∧ (0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length) ∧
  (∀ s ∈ shards, s.shard_offsets.length=s.shard_sizes.length ∧ s.shard_offsets.length=(shards.getD 0 default).shard_offsets.length) ∧
  order.Perm (VeriPy.range 0 (Int.ofNat shards.length)) ∧
  order.Pairwise (fun a b => a≠b ∧ Start shards d a≤Start shards d b)

def ActiveLex (a b : Int × Int) : Bool := decide (a.1<b.1 ∨ a.1=b.1 ∧ a.2≤b.2)

def ActiveState (shards : List ShardMetadata) (order : List Int) (k d : Int) (active : List (Int × Int)) : Prop :=
  (0≤k ∧ k≤Int.ofNat order.length) ∧
  (∀ v ∈ active, (0≤v.2 ∧ v.2<Int.ofNat shards.length) ∧ v.2∈order.take k.toNat ∧ v.1=End shards d v.2) ∧
  active.Pairwise (fun a b => ActiveLex a b) ∧
  (∀ a ∈ order.take k.toNat, k<Int.ofNat order.length → End shards d a>Start shards d (Read order k) → (End shards d a,a)∈active)

def ProcessedDisjoint (shards : List ShardMetadata) (order : List Int) (k : Int) : Prop :=
  ∀ a ∈ order.take k.toNat, ∀ b ∈ order.take k.toNat, a≠b → ¬ShardsOverlap (Read shards a) (Read shards b)

def Scanned (shards : List ShardMetadata) (idx : Int) (active : List (Int × Int)) (k : Int) : Prop :=
  ∀ a ∈ active.take k.toNat, ¬ShardsOverlap (Read shards idx) (Read shards a.2)

-- VERIPY PRELUDE END


theorem PairInit (a b : ShardMetadata) (n : Int) :
    _check_shard_metadata_pair_overlap__inv_22 a b n 0 := by
  unfold _check_shard_metadata_pair_overlap__inv_22
  intro j hj; omega

theorem PairStep (a b : ShardMetadata) (n i : Int)
    (h : _check_shard_metadata_pair_overlap__inv_22 a b n i)
    (left : ¬ a.shard_offsets.getD i.toNat default ≥ b.shard_offsets.getD i.toNat default + b.shard_sizes.getD i.toNat default)
    (right : ¬ b.shard_offsets.getD i.toNat default ≥ a.shard_offsets.getD i.toNat default + a.shard_sizes.getD i.toNat default) :
    _check_shard_metadata_pair_overlap__inv_22 a b n (i+1) := by
  intro j hj
  by_cases he : j = i
  · subst j; constructor <;> omega
  · exact h j (by omega)

theorem PairPost (a b : ShardMetadata) (n : Int)
    (h : _check_shard_metadata_pair_overlap__inv_22 a b n (Int.ofNat a.shard_offsets.length)) :
    _check_shard_metadata_pair_overlap__post a b true := by
  unfold _check_shard_metadata_pair_overlap__post
  constructor
  · intro _; simpa only [_check_shard_metadata_pair_overlap__inv_22, Int.zero_add] using h
  · intro _; rfl


theorem RangeLength (n : Nat) : (VeriPy.range 0 (Int.ofNat n)).length = n := by
  simp [VeriPy.range]

theorem PairStepCursor (a b : ShardMetadata) (n cur i : Int) (pre suf : List Int)
    (hr : VeriPy.range 0 n = pre ++ cur :: suf) (hi : i = Int.ofNat pre.length)
    (h : _check_shard_metadata_pair_overlap__inv_22 a b n i)
    (left : ¬ a.shard_offsets.getD cur.toNat default ≥ b.shard_offsets.getD cur.toNat default + b.shard_sizes.getD cur.toNat default)
    (right : ¬ b.shard_offsets.getD cur.toNat default ≥ a.shard_offsets.getD cur.toNat default + a.shard_sizes.getD cur.toNat default) :
    _check_shard_metadata_pair_overlap__inv_22 a b n (i+1) := by
  have he : cur = i := (RangeCursor n cur pre suf hr).1.trans hi.symm
  subst cur
  exact PairStep a b n i h left right

theorem RangeFailure (n cur : Int) (pre suf : List Int)
    (h : VeriPy.range 0 n = pre ++ cur :: suf)
    (bad : ¬ (0 ≤ cur ∧ cur < n)) : False := by
  exact bad (RangeCursor n cur pre suf h).2

theorem LexHead (a b : Int) (as bs : List Int) (h : VeriPy.lexInts (a::as) (b::bs)) : a≤b := by
  unfold VeriPy.lexInts at h
  split at h
  · omega
  · split at h
    · omega
    · contradiction

theorem LexIntsTrans (a b c : List Int) (hab : VeriPy.lexInts a b) (hbc : VeriPy.lexInts b c) : VeriPy.lexInts a c := by
  induction a generalizing b c with
  | nil => rfl
  | cons a as ih =>
    cases b with
    | nil => contradiction
    | cons b bs =>
      cases c with
      | nil => contradiction
      | cons c cs =>
        have h1:=LexHead a b as bs hab
        have h2:=LexHead b c bs cs hbc
        by_cases hlt : a<c
        · simp only [VeriPy.lexInts,if_pos hlt]
        · have hab' : a=b := by omega
          have hbc' : b=c := by omega
          subst b; subst c
          simp only [VeriPy.lexInts,Int.lt_irrefl,if_false,if_true] at hab hbc ⊢
          exact ih bs cs hab hbc

theorem LexIntsTotal (a b : List Int) : VeriPy.lexInts a b || VeriPy.lexInts b a := by
  induction a generalizing b with
  | nil => rfl
  | cons a as ih =>
    cases b with
    | nil => rfl
    | cons b bs =>
      by_cases hlt : a<b
      · simp only [VeriPy.lexInts,if_pos hlt,Bool.true_or]
      · by_cases hgt : b<a
        · simp only [VeriPy.lexInts,if_pos hgt,Bool.or_true]
        · have he : a=b := by omega
          subst b
          simpa only [VeriPy.lexInts,Int.lt_irrefl,if_false,if_true] using ih bs

theorem BisectAuxFacts [Inhabited α] (le : α → α → Bool) (xs : List α) (x : α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (ordered : xs.Pairwise (fun a b => le a b))
    (fuel lo hi : Nat) (bounds : lo≤hi ∧ hi≤xs.length) (budget : hi-lo<fuel)
    (before : ∀ i : Nat, (h : i<lo) → le xs[i] x)
    (suffix : ∀ i : Nat, (h : i<xs.length) → hi≤i → ¬le xs[i] x) :
    let result := VeriPy.bisectRightAux le xs x fuel lo hi
    (lo≤result ∧ result≤hi) ∧
    (∀ i : Nat, (h : i<xs.length) → i<result → le xs[i] x) ∧
    (∀ i : Nat, (h : i<xs.length) → result≤i → ¬le xs[i] x) := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    by_cases active : lo<hi
    · have midlo : lo≤(lo+hi)/2 := by omega
      have midhi : (lo+hi)/2<hi := by omega
      have midlen : (lo+hi)/2<xs.length := by omega
      have read : xs.getD ((lo+hi)/2) default=xs[(lo+hi)/2] := by simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem midlen,Option.getD_some]
      simp only [VeriPy.bisectRightAux,if_pos active,read]
      split
      next yes =>
        have p : ∀ i : Nat, (h : i<(lo+hi)/2+1) → le xs[i] x := by
          intro i hi'
          by_cases he : i=(lo+hi)/2
          · subst i; exact yes
          · have order:=List.pairwise_iff_getElem.mp ordered i ((lo+hi)/2) (by omega) midlen (by omega)
            exact trans _ _ _ order yes
        have got:=ih ((lo+hi)/2+1) hi ⟨by omega,bounds.2⟩ (by omega) p suffix
        exact ⟨⟨by have := got.1; omega,got.1.2⟩,got.2⟩
      next no =>
        have s : ∀ i : Nat, (h : i<xs.length) → (lo+hi)/2≤i → ¬le xs[i] x := by
          intro i hi' lower hx
          by_cases he : i=(lo+hi)/2
          · subst i; exact no hx
          · have order:=List.pairwise_iff_getElem.mp ordered ((lo+hi)/2) i midlen hi' (by omega)
            exact no (trans _ _ _ order hx)
        have got:=ih lo ((lo+hi)/2) ⟨midlo,by omega⟩ (by omega) before s
        exact ⟨⟨got.1.1,by have := got.1; omega⟩,got.2⟩
    · have he : hi=lo := by omega
      simp only [VeriPy.bisectRightAux,if_neg active]
      exact ⟨⟨Nat.le_refl _,by omega⟩,(fun i _ hi => before i hi),by simpa only [he] using suffix⟩

theorem BisectFacts [Inhabited α] (le : α → α → Bool) (xs : List α) (x : α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (ordered : xs.Pairwise (fun a b => le a b)) :
    let cut := VeriPy.bisectRight le xs x
    cut≤xs.length ∧
    (∀ i : Nat, (h : i<xs.length) → i<cut → le xs[i] x) ∧
    (∀ i : Nat, (h : i<xs.length) → cut≤i → ¬le xs[i] x) := by
  have h:=BisectAuxFacts le xs x trans ordered (xs.length+1) 0 xs.length ⟨Nat.zero_le _,Nat.le_refl _⟩ (by omega)
    (fun i hi => by omega) (fun i hi lower => by omega)
  exact ⟨h.1.2,h.2⟩

theorem BisectBefore [Inhabited α] (le : α → α → Bool) (xs : List α) (x a : α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (ordered : xs.Pairwise (fun a b => le a b))
    (ha : a∈xs.take (VeriPy.bisectRight le xs x)) : le a x := by
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp ha
  have bounds : i<xs.length ∧ i<VeriPy.bisectRight le xs x := by simp only [List.length_take] at hi; omega
  have read : (xs.take (VeriPy.bisectRight le xs x))[i]=xs[i] := List.getElem_take
  rw [read] at he
  rw [←he]
  exact (BisectFacts le xs x trans ordered).2.1 i bounds.1 bounds.2

theorem BisectAfter [Inhabited α] (le : α → α → Bool) (xs : List α) (x a : α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (ordered : xs.Pairwise (fun a b => le a b))
    (ha : a∈xs.drop (VeriPy.bisectRight le xs x)) : ¬le a x := by
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp ha
  have bounds : VeriPy.bisectRight le xs x+i<xs.length := by simp only [List.length_drop] at hi; omega
  have read : (xs.drop (VeriPy.bisectRight le xs x))[i]=xs[VeriPy.bisectRight le xs x+i] := List.getElem_drop
  rw [read] at he
  rw [←he]
  exact (BisectFacts le xs x trans ordered).2.2 _ bounds (by omega)

theorem InsortOrdered [Inhabited α] (le : α → α → Bool) (xs : List α) (x : α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a)
    (ordered : xs.Pairwise (fun a b => le a b)) :
    (VeriPy.insort le xs x).Pairwise (fun a b => le a b) := by
  have before := BisectBefore le xs x
  have after : ∀ a∈xs.drop (VeriPy.bisectRight le xs x), le x a := by
    intro a ha
    have h:=BisectAfter le xs x a trans ordered ha
    have t:=total a x
    simp only [Bool.or_eq_true] at t
    exact t.resolve_left h
  unfold VeriPy.insort
  apply List.pairwise_append.mpr
  refine ⟨ordered.take,List.pairwise_cons.mpr ⟨after,ordered.drop⟩,?_⟩
  intro a ha b hb
  have hax:=before a trans ordered ha
  rcases List.mem_cons.mp hb with he | hb
  · subst b; exact hax
  · exact trans _ _ _ hax (after b hb)

theorem InsortMembers [Inhabited α] (le : α → α → Bool) (xs : List α) (x a : α) :
    a∈VeriPy.insort le xs x ↔ a=x ∨ a∈xs := by
  unfold VeriPy.insort
  rw [List.mem_append,List.mem_cons]
  have h : a∈xs.take (VeriPy.bisectRight le xs x) ∨ a∈xs.drop (VeriPy.bisectRight le xs x) ↔ a∈xs := by
    rw [←List.mem_append,List.take_append_drop]
  grind only

def Key (shards : List ShardMetadata) (dims : List Int) (d i : Int) : List Int :=
  Start shards d i :: (dims.filter (fun k => decide (k≠d))).map (fun k=>Read (Read shards i).shard_offsets k)

def SortedOrder (shards : List ShardMetadata) (dims : List Int) (d : Int) : List Int :=
  (((VeriPy.range 0 (Int.ofNat shards.length)).map (fun i=>(Key shards dims d i,i))).mergeSort
    (fun a b=>VeriPy.lexInts a.1 b.1)).map Prod.snd

theorem OrderPerm (shards : List ShardMetadata) (dims : List Int) (d : Int) :
    (SortedOrder shards dims d).Perm (VeriPy.range 0 (Int.ofNat shards.length)) := by
  have h:=(List.mergeSort_perm ((VeriPy.range 0 (Int.ofNat shards.length)).map (fun i=>(Key shards dims d i,i))) (fun a b=>VeriPy.lexInts a.1 b.1)).map Prod.snd
  simp only [List.map_map] at h
  change (SortedOrder shards dims d).Perm ((VeriPy.range 0 (Int.ofNat shards.length)).map id) at h
  simpa only [List.map_id] using h

theorem RangeMember (n i : Int) : i∈VeriPy.range 0 n ↔ 0≤i ∧ i<n := by
  simp only [VeriPy.range,Int.sub_zero,List.mem_map]
  constructor
  · rintro ⟨k,hk,he⟩
    simp only [Int.zero_add] at he
    subst i
    have hb:=List.mem_range.mp hk
    simp only [VeriPy.ofNat_cast]
    omega
  · intro hi
    refine ⟨i.toNat,List.mem_range.mpr (by omega),?_⟩
    change (0:Int)+(i.toNat:Int)=i
    rw [Int.zero_add]
    exact Int.toNat_of_nonneg hi.1

theorem RangeDistinct (n : Nat) : (VeriPy.range 0 (Int.ofNat n)).Nodup := by
  simp only [VeriPy.range,Int.sub_zero,Int.zero_add]
  change ((List.range n).map Int.ofNat).Pairwise (fun a b => a≠b)
  rw [List.pairwise_map]
  exact List.nodup_range.imp (fun h he=>h (Int.ofNat.inj he))

theorem OrderStarts (shards : List ShardMetadata) (dims : List Int) (d : Int) :
    (SortedOrder shards dims d).Pairwise (fun a b => a≠b ∧ Start shards d a≤Start shards d b) := by
  have nd : (SortedOrder shards dims d).Nodup := (OrderPerm shards dims d).nodup_iff.mpr (RangeDistinct _)
  apply nd.and
  unfold SortedOrder
  rw [List.pairwise_map]
  have sorted:=List.pairwise_mergeSort (fun a b c=>LexIntsTrans a.1 b.1 c.1) (fun a b=>LexIntsTotal a.1 b.1)
    ((VeriPy.range 0 (Int.ofNat shards.length)).map (fun i=>(Key shards dims d i,i)))
  apply sorted.imp_of_mem
  intro a b ha hb hab
  have perm:=List.mergeSort_perm ((VeriPy.range 0 (Int.ofNat shards.length)).map (fun i=>(Key shards dims d i,i))) (fun a b=>VeriPy.lexInts a.1 b.1)
  obtain ⟨i,hi,hei⟩:=List.mem_map.mp (perm.mem_iff.mp ha)
  obtain ⟨j,hj,hej⟩:=List.mem_map.mp (perm.mem_iff.mp hb)
  subst a; subst b
  exact LexHead _ _ _ _ hab

theorem OrderDomain (shards : List ShardMetadata) (dims : List Int) (d : Int)
    (nonempty : shards≠[])
    (hd : 0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (ranks : ∀ s∈shards, s.shard_offsets.length=s.shard_sizes.length ∧ s.shard_offsets.length=(shards.getD 0 default).shard_offsets.length) :
    SweepDomain shards (SortedOrder shards dims d) d :=
  ⟨nonempty,hd,ranks,OrderPerm shards dims d,OrderStarts shards dims d⟩

theorem ActiveTrans (a b c : Int × Int) (hab : ActiveLex a b) (hbc : ActiveLex b c) : ActiveLex a c := by
  simp only [ActiveLex,decide_eq_true_eq] at *
  omega

theorem ActiveTotal (a b : Int × Int) : ActiveLex a b || ActiveLex b a := by
  simp only [ActiveLex,Bool.or_eq_true,decide_eq_true_eq]
  omega

theorem ReadNonnegative [Inhabited α] (xs : List α) (i : Int) (hi : 0≤i) : Read xs i=xs.getD i.toNat default := by
  simp only [Read,if_neg (show ¬i<0 by omega)]

theorem ReadMember [Inhabited α] (xs : List α) (i : Int) (hi : 0≤i ∧ i<Int.ofNat xs.length) : Read xs i∈xs := by
  rw [ReadNonnegative xs i hi.1]
  have hb : i.toNat<xs.length := by change 0≤i ∧ i<(xs.length:Int) at hi; omega
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb,Option.getD_some]
  exact List.getElem_mem hb

theorem TakeNext [Inhabited α] (xs : List α) (i : Int) (hi : 0≤i ∧ i<Int.ofNat xs.length) :
    xs.take (i+1).toNat=xs.take i.toNat++[Read xs i] := by
  have hb : i.toNat<xs.length := by change 0≤i ∧ i<(xs.length:Int) at hi; omega
  have he : (i+1).toNat=i.toNat+1 := by omega
  rw [he,List.take_succ_eq_append_getElem hb,ReadNonnegative xs i hi.1]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb,Option.getD_some]

theorem DomainMember (shards : List ShardMetadata) (order : List Int) (d i : Int)
    (domain : SweepDomain shards order d) (member : i∈order) :
    (0≤i ∧ i<Int.ofNat shards.length) ∧
    (Read shards i).shard_offsets.length=(Read shards i).shard_sizes.length ∧
    (0≤d ∧ d<Int.ofNat (Read shards i).shard_offsets.length) := by
  have hi := (RangeMember _ _).mp (domain.2.2.2.1.mem_iff.mp member)
  have ranks := domain.2.2.1 _ (ReadMember shards i hi)
  exact ⟨hi,ranks.1,by rw [ranks.2]; exact domain.2.1⟩

theorem ActiveSuffix (shards : List ShardMetadata) (order : List Int) (k d : Int) (active : List (Int × Int))
    (state : ActiveState shards order k d active) :
    ActiveState shards order k d (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d (Read order k),9223372036854775807))) := by
  refine ⟨state.1,?_,state.2.2.1.drop,?_⟩
  · intro v hv
    exact state.2.1 v (List.mem_of_mem_drop hv)
  · intro a ha hk overlap
    have member:=state.2.2.2 a ha hk overlap
    have all : (End shards d a,a)∈active.take (VeriPy.bisectRight ActiveLex active (Start shards d (Read order k),9223372036854775807)) ∨
      (End shards d a,a)∈active.drop (VeriPy.bisectRight ActiveLex active (Start shards d (Read order k),9223372036854775807)) := by
      rw [←List.mem_append,List.take_append_drop]; exact member
    rcases all with before | after
    · have h:=BisectBefore ActiveLex active (Start shards d (Read order k),9223372036854775807) (End shards d a,a) ActiveTrans state.2.2.1 before
      simp only [ActiveLex,decide_eq_true_eq] at h
      omega
    · exact after

theorem ActiveEmpty (shards : List ShardMetadata) (order : List Int) (d : Int) :
    ActiveState shards order 0 d [] := by
  refine ⟨⟨by omega,Int.natCast_nonneg _⟩,?_,by constructor,?_⟩
  · simp
  · simp

theorem ScannedEmpty (shards : List ShardMetadata) (idx : Int) (active : List (Int × Int)) : Scanned shards idx active 0 := by
  simp only [Scanned,show (0:Int).toNat=0 by rfl,List.take_zero,List.not_mem_nil,false_implies,implies_true]

theorem ProcessedEmpty (shards : List ShardMetadata) (order : List Int) : ProcessedDisjoint shards order 0 := by
  simp only [ProcessedDisjoint,show (0:Int).toNat=0 by rfl,List.take_zero,List.not_mem_nil,false_implies,implies_true]

theorem OverlapSymmetric (a b : ShardMetadata) : ShardsOverlap a b ↔ ShardsOverlap b a := by
  constructor <;> intro h
  · refine ⟨h.2.1,h.1,h.2.2.1.symm,?_⟩
    intro d hd
    have got:=h.2.2.2 d (by rw [h.2.2.1];exact hd)
    exact ⟨got.2,got.1⟩
  · refine ⟨h.2.1,h.1,h.2.2.1.symm,?_⟩
    intro d hd
    have got:=h.2.2.2 d (by rw [h.2.2.1];exact hd)
    exact ⟨got.2,got.1⟩

theorem ScannedStep (shards : List ShardMetadata) (idx k : Int) (active : List (Int × Int))
    (hk : 0≤k ∧ k<Int.ofNat active.length)
    (state : Scanned shards idx active k)
    (separated : ¬ShardsOverlap (Read shards idx) (Read shards (Read active k).2)) :
    Scanned shards idx active (k+1) := by
  intro a ha
  rw [TakeNext active k hk,List.mem_append,List.mem_singleton] at ha
  rcases ha with ha | he
  · exact state a ha
  · subst a; exact separated

theorem OrderReadNext (shards : List ShardMetadata) (order : List Int) (d k : Int)
    (domain : SweepDomain shards order d) (hk : 0≤k ∧ k+1<Int.ofNat order.length) :
    Start shards d (Read order k)≤Start shards d (Read order (k+1)) := by
  have h0 : k.toNat<order.length := by change 0≤k ∧ k+1<(order.length:Int) at hk; omega
  have h1 : (k+1).toNat<order.length := by change 0≤k ∧ k+1<(order.length:Int) at hk; omega
  have hl : k.toNat<(k+1).toNat := by omega
  have orderFact:=List.pairwise_iff_getElem.mp domain.2.2.2.2 k.toNat (k+1).toNat h0 h1 hl
  rw [ReadNonnegative order k hk.1,ReadNonnegative order (k+1) (by omega)]
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1,Option.getD_some] using orderFact.2

theorem ActiveInsert (shards : List ShardMetadata) (order : List Int) (k d : Int) (active : List (Int × Int))
    (domain : SweepDomain shards order d) (state : ActiveState shards order k d active)
    (hk : k<Int.ofNat order.length) :
    ActiveState shards order (k+1) d (VeriPy.insort ActiveLex active (End shards d (Read order k),Read order k)) := by
  have hb : 0≤k ∧ k<Int.ofNat order.length := ⟨state.1.1,hk⟩
  have current := DomainMember shards order d (Read order k) domain (ReadMember order k hb)
  refine ⟨⟨by omega,by omega⟩,?_,InsortOrdered ActiveLex active _ ActiveTrans ActiveTotal state.2.2.1,?_⟩
  · intro v hv
    rw [InsortMembers] at hv
    rw [TakeNext order k hb]
    rcases hv with he | hv
    · subst v
      exact ⟨current.1,by simp,rfl⟩
    · have h:=state.2.1 v hv
      exact ⟨h.1,List.mem_append.mpr (Or.inl h.2.1),h.2.2⟩
  · intro a ha hn overlap
    rw [TakeNext order k hb,List.mem_append,List.mem_singleton] at ha
    rw [InsortMembers]
    rcases ha with ha | he
    · right
      apply state.2.2.2 a ha hk
      have next := OrderReadNext shards order d k domain ⟨state.1.1,hn⟩
      omega
    · subst a; exact Or.inl rfl

theorem SeparatedExpired (shards : List ShardMetadata) (order : List Int) (d a b : Int)
    (domain : SweepDomain shards order d) (ha : a∈order)
    (expired : End shards d a≤Start shards d b) : ¬ShardsOverlap (Read shards a) (Read shards b) := by
  intro overlap
  have valid:=DomainMember shards order d a domain ha
  have opposite:=(overlap.2.2.2 d valid.2.2).2
  change Read (Read shards b).shard_offsets d < Start shards d a+Read (Read shards a).shard_sizes d at opposite
  change Start shards d a+Read (Read shards a).shard_sizes d≤Read (Read shards b).shard_offsets d at expired
  omega

theorem SweepStep (shards : List ShardMetadata) (order : List Int) (k d : Int) (active : List (Int × Int))
    (domain : SweepDomain shards order d) (state : ActiveState shards order k d active)
    (processed : ProcessedDisjoint shards order k)
    (scanned : Scanned shards (Read order k) active (Int.ofNat active.length))
    (hk : k<Int.ofNat order.length) : ProcessedDisjoint shards order (k+1) := by
  have hb : 0≤k ∧ k<Int.ofNat order.length := ⟨state.1.1,hk⟩
  have previous : ∀ a∈order.take k.toNat, ¬ShardsOverlap (Read shards a) (Read shards (Read order k)) := by
    intro a ha
    by_cases expired : End shards d a≤Start shards d (Read order k)
    · exact SeparatedExpired shards order d a (Read order k) domain (List.mem_of_mem_take ha) expired
    · have activeMember:=state.2.2.2 a ha hk (by omega)
      have hs:=scanned (End shards d a,a) (by simpa only [show (Int.ofNat active.length).toNat=active.length by rfl,List.take_length] using activeMember)
      exact fun h => hs ((OverlapSymmetric _ _).mp h)
  intro a ha b hb' distinct
  rw [TakeNext order k hb,List.mem_append,List.mem_singleton] at ha hb'
  rcases ha with ha | he
  · rcases hb' with hb' | he
    · exact processed a ha b hb' distinct
    · subst b; exact previous a ha
  · subst a
    rcases hb' with hb' | he
    · exact fun h => previous b hb' ((OverlapSymmetric _ _).mp h)
    · subst b; exact False.elim (distinct rfl)

theorem AllPairs (shards : List ShardMetadata) (order : List Int) (d : Int)
    (domain : SweepDomain shards order d)
    (processed : ProcessedDisjoint shards order (Int.ofNat order.length)) :
    ∀ a b : Int, (0≤a ∧ a<Int.ofNat shards.length) → (0≤b ∧ b<Int.ofNat shards.length) → a≠b → ¬ShardsOverlap (Read shards a) (Read shards b) := by
  intro a b ha hb distinct
  have ma:=domain.2.2.2.1.mem_iff.mpr ((RangeMember _ _).mpr ha)
  have mb:=domain.2.2.2.1.mem_iff.mpr ((RangeMember _ _).mpr hb)
  apply processed a _ b _ distinct
  · simpa only [show (Int.ofNat order.length).toNat=order.length by rfl,List.take_length] using ma
  · simpa only [show (Int.ofNat order.length).toNat=order.length by rfl,List.take_length] using mb

def Ranks (shards : List ShardMetadata) : Prop :=
  ∀ a : Int, (0≤a ∧ a<Int.ofNat shards.length) →
    Int.ofNat (shards.getD a.toNat default).shard_offsets.length=Int.ofNat (shards.getD a.toNat default).shard_sizes.length ∧
    Int.ofNat (shards.getD a.toNat default).shard_offsets.length=Int.ofNat (shards.getD 0 default).shard_offsets.length

theorem RanksMember (shards : List ShardMetadata) (s : ShardMetadata) (ranks : Ranks shards) (member : s∈shards) :
    s.shard_offsets.length=s.shard_sizes.length ∧ s.shard_offsets.length=(shards.getD 0 default).shard_offsets.length := by
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp member
  have h:=ranks (Int.ofNat i) ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hi⟩
  have read : shards.getD (Int.ofNat i).toNat default=s := by
    simpa only [show (Int.ofNat i).toNat=i by rfl,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using he
  rw [read] at h
  exact ⟨Int.ofNat.inj h.1,Int.ofNat.inj h.2⟩

theorem SelectedDimension (shards : List ShardMetadata) (dims : List Int) (k : Int)
    (ranks : Ranks shards) (hk : 0≤k ∧ k<Int.ofNat dims.length)
    (valid : ∀ j : Int, (0≤j ∧ j<Int.ofNat dims.length) → 0≤Read dims j ∧ Read dims j<Int.ofNat (shards.getD 0 default).shard_offsets.length) :
    ∀ s∈shards, (0≤Read dims k ∧ Read dims k<Int.ofNat s.shard_offsets.length) ∧ s.shard_offsets.length=s.shard_sizes.length := by
  intro s hs
  have h:=RanksMember shards s ranks hs
  exact ⟨by rw [h.2];exact valid k hk,h.1⟩

theorem SearchOverlapWitness (shards : List ShardMetadata) (a b : Int)
    (ranks : Ranks shards) (ha : 0≤a ∧ a<Int.ofNat shards.length) (hb : 0≤b ∧ b<Int.ofNat shards.length)
    (overlap : ∀ d : Int, (0≤d ∧ d<Int.ofNat (shards.getD a.toNat default).shard_offsets.length) →
      (shards.getD a.toNat default).shard_offsets.getD d.toNat default <
        (shards.getD b.toNat default).shard_offsets.getD d.toNat default+(shards.getD b.toNat default).shard_sizes.getD d.toNat default ∧
      (shards.getD b.toNat default).shard_offsets.getD d.toNat default <
        (shards.getD a.toNat default).shard_offsets.getD d.toNat default+(shards.getD a.toNat default).shard_sizes.getD d.toNat default) :
    ShardsOverlap (Read shards a) (Read shards b) := by
  rw [ReadNonnegative shards a ha.1,ReadNonnegative shards b hb.1]
  have ra:=ranks a ha;have rb:=ranks b hb
  refine ⟨Int.ofNat.inj ra.1,Int.ofNat.inj rb.1,Int.ofNat.inj (ra.2.trans rb.2.symm),?_⟩
  intro d hd
  simpa only [Read,if_neg (show ¬d<0 by omega)] using overlap d hd

theorem SearchComplete (shards : List ShardMetadata) (dims order : List Int) (d : Int)
    (ranks : Ranks shards) (domain : SweepDomain shards order d)
    (processed : ProcessedDisjoint shards order (Int.ofNat order.length)) :
    _find_nd_overlapping_shards__post shards dims none := by
  simp only [_find_nd_overlapping_shards__post,ne_eq,reduceCtorEq,not_false_eq_true,not_true_eq_false,true_or,true_and,false_or]
  rintro ⟨a,ha,b,hb,distinct,overlap⟩
  exact AllPairs shards order d domain processed a b ha hb distinct (SearchOverlapWitness shards a b ranks ha hb overlap)

theorem SearchTrivial (shards : List ShardMetadata) (dims : List Int) (small : Int.ofNat shards.length≤1) :
    _find_nd_overlapping_shards__post shards dims none := by
  simp only [_find_nd_overlapping_shards__post,ne_eq,reduceCtorEq,not_false_eq_true,not_true_eq_false,true_or,true_and,false_or]
  rintro ⟨a,ha,b,hb,distinct,_⟩
  omega

theorem CheckedRead [Inhabited α] (xs : List α) (i : Int) (hi : 0≤i ∧ i<Int.ofNat xs.length) :
    VeriPy.getPython xs i=Except.ok (Read xs i) := by
  have hn : ¬i<0 := by omega
  change 0≤i ∧ i<(xs.length:Int) at hi
  simp only [VeriPy.getPython,Read,if_neg hn,VeriPy.get,if_pos hi]
  rfl

theorem CheckedMap (xs : List α) (f : α → Except VeriPy.Error β) (model : α → β)
    (h : ∀ x∈xs, f x=Except.ok (model x)) : VeriPy.mapChecked f model xs=Except.ok (xs.map model) := by
  unfold VeriPy.mapChecked
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have head:=h x (by simp)
    have tail:=ih (fun a ha=>h a (by simp [ha]))
    rw [List.mapM_cons,head,tail]
    rfl

def Dimensions (shards : List ShardMetadata) (dims : List Int) : Prop :=
  ∀ d∈dims, 0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length

theorem DimensionsFromIndices (shards : List ShardMetadata) (dims : List Int)
    (valid : ∀ j : Int, (0≤j ∧ j<Int.ofNat dims.length) →
      0≤dims.getD j.toNat default ∧ dims.getD j.toNat default<Int.ofNat (shards.getD 0 default).shard_offsets.length) : Dimensions shards dims := by
  intro d hd
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hd
  have h:=valid (Int.ofNat i) ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hi⟩
  simpa only [show (Int.ofNat i).toNat=i by rfl,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he] using h

theorem BuildKey (shards : List ShardMetadata) (dims : List Int) (d i : Int)
    (ranks : Ranks shards) (dimensions : Dimensions shards dims)
    (hd : 0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (hi : 0≤i ∧ i<Int.ofNat shards.length) :
    (do return ([(← VeriPy.getPython (← VeriPy.getPython shards i).shard_offsets d)] ++
      (← VeriPy.mapChecked (fun k => (do return (← VeriPy.getPython (← VeriPy.getPython shards i).shard_offsets k) : Except VeriPy.Error Int))
        (fun k=>Read (Read shards i).shard_offsets k) (dims.filter (fun k=>decide (k≠d)))),i) : Except VeriPy.Error (List Int × Int)) =
      Except.ok (Key shards dims d i,i) := by
  have sr:=CheckedRead shards i hi
  have rank:=RanksMember shards (Read shards i) ranks (ReadMember shards i hi)
  have dr:=CheckedRead (Read shards i).shard_offsets d (by rw [rank.2];exact hd)
  have rest : VeriPy.mapChecked (fun k => (do return (← VeriPy.getPython (← VeriPy.getPython shards i).shard_offsets k) : Except VeriPy.Error Int))
        (fun k=>Read (Read shards i).shard_offsets k) (dims.filter (fun k=>decide (k≠d))) =
      Except.ok ((dims.filter (fun k=>decide (k≠d))).map (fun k=>Read (Read shards i).shard_offsets k)) := by
    apply CheckedMap
    intro k hk
    have kb:=dimensions k (List.mem_filter.mp hk).1
    have kr:=CheckedRead (Read shards i).shard_offsets k (by rw [rank.2];exact kb)
    rw [sr]
    change (do return (← VeriPy.getPython (Read shards i).shard_offsets k) : Except VeriPy.Error Int)=_
    rw [kr]
  rw [rest,sr]
  change (do return ([← VeriPy.getPython (Read shards i).shard_offsets d] ++ _,i) : Except VeriPy.Error (List Int × Int))=_
  rw [dr];rfl

theorem NDChooseInit (shards : List ShardMetadata) (dims : List Int) (count : Int)
    (positive : 0<Int.ofNat dims.length) :
    _find_nd_overlapping_shards__inv_53 shards dims count 0 0 0 := by
  exact ⟨by omega,positive⟩

theorem NDChooseStep (shards : List ShardMetadata) (dims pre suf : List Int) (count maximum i cur : Int)
    (cursor : dims=pre++cur::suf) (hi : i=Int.ofNat pre.length) :
    _find_nd_overlapping_shards__inv_53 shards dims count i maximum (i+1) := by
  constructor
  · rw [hi];exact Int.natCast_nonneg _
  · rw [hi,cursor,List.length_append,List.length_cons]
    simp only [VeriPy.ofNat_cast,Int.natCast_add,Int.natCast_one]
    omega

theorem NDInnerInit (shards : List ShardMetadata) (dims : List Int) (count selected d : Int) (order : List Int)
    (active : List (Int × Int)) (outer idx : Int) (current : ShardMetadata) (start ending cutoff : Int) :
    _find_nd_overlapping_shards__inv_84 shards dims count selected d order active outer idx current start ending cutoff 0 :=
  ScannedEmpty shards idx active

theorem DimensionsAvailable (shards : List ShardMetadata) (dims : List Int)
    (nonempty : Int.ofNat shards.length>0)
    (valid : Int.ofNat shards.length=0 ∨ ∀ j : Int, (0≤j ∧ j<Int.ofNat dims.length) →
      0≤dims.getD j.toNat default ∧ dims.getD j.toNat default<Int.ofNat (shards.getD 0 default).shard_offsets.length) : Dimensions shards dims := by
  rcases valid with empty | valid
  · omega
  · exact DimensionsFromIndices shards dims valid

theorem DimensionCursor (shards : List ShardMetadata) (dims pre suf : List Int) (d : Int)
    (cursor : dims=pre++d::suf) (dimensions : Dimensions shards dims) :
    0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length := by
  apply dimensions d
  rw [cursor];simp

theorem NDChooseInvalidOffset (shards : List ShardMetadata) (dims pre suf : List Int) (d : Int)
    (cursor : dims=pre++d::suf) (nonempty : Int.ofNat shards.length>0)
    (valid : Int.ofNat shards.length=0 ∨ ∀ j : Int, (0≤j ∧ j<Int.ofNat dims.length) →
      0≤dims.getD j.toNat default ∧ dims.getD j.toNat default<Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (bad : ¬(0≤(if d<0 then Int.ofNat (shards.getD 0 default).shard_offsets.length+d else d) ∧
      (if d<0 then Int.ofNat (shards.getD 0 default).shard_offsets.length+d else d)<Int.ofNat (shards.getD 0 default).shard_offsets.length)) : False := by
  have h:=DimensionCursor shards dims pre suf d cursor (DimensionsAvailable shards dims nonempty valid)
  rw [if_neg (show ¬d<0 by omega)] at bad
  exact bad h

theorem NDChooseInvalidSize (shards : List ShardMetadata) (dims pre suf : List Int) (d : Int)
    (cursor : dims=pre++d::suf) (nonempty : Int.ofNat shards.length>0) (ranks : Ranks shards)
    (valid : Int.ofNat shards.length=0 ∨ ∀ j : Int, (0≤j ∧ j<Int.ofNat dims.length) →
      0≤dims.getD j.toNat default ∧ dims.getD j.toNat default<Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (bad : ¬(0≤(if d<0 then Int.ofNat (shards.getD 0 default).shard_sizes.length+d else d) ∧
      (if d<0 then Int.ofNat (shards.getD 0 default).shard_sizes.length+d else d)<Int.ofNat (shards.getD 0 default).shard_sizes.length)) : False := by
  have h:=DimensionCursor shards dims pre suf d cursor (DimensionsAvailable shards dims nonempty valid)
  have rank:=(ranks 0 ⟨by omega,nonempty⟩).1
  rw [if_neg (show ¬d<0 by omega)] at bad
  apply bad
  simp only [show (0:Int).toNat=0 by rfl] at rank
  exact ⟨h.1,by rw [←rank];exact h.2⟩

theorem NDMapRows (shards : List ShardMetadata) (dims : List Int) (selected : Int)
    (nonempty : Int.ofNat shards.length>0) (ranks : Ranks shards)
    (valid : Int.ofNat shards.length=0 ∨ ∀ j : Int, (0≤j ∧ j<Int.ofNat dims.length) →
      0≤dims.getD j.toNat default ∧ dims.getD j.toNat default<Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (hs : 0≤selected ∧ selected<Int.ofNat dims.length) :
    ∀ i∈VeriPy.range 0 (Int.ofNat shards.length),
    (do return ([(← VeriPy.getPython (← VeriPy.getPython shards i).shard_offsets (Read dims selected))] ++
      (← VeriPy.mapChecked (fun k => (do return (← VeriPy.getPython (← VeriPy.getPython shards i).shard_offsets k) : Except VeriPy.Error Int))
        (fun k=>Read (Read shards i).shard_offsets k) (dims.filter (fun k=>decide (k≠Read dims selected)))),i) : Except VeriPy.Error (List Int × Int)) =
      Except.ok (Key shards dims (Read dims selected) i,i) := by
  intro i hi
  have dimensions:=DimensionsAvailable shards dims nonempty valid
  exact BuildKey shards dims (Read dims selected) i ranks dimensions (dimensions _ (ReadMember dims selected hs)) ((RangeMember _ _).mp hi)

theorem NDOuterInit (shards : List ShardMetadata) (dims : List Int) (count selected d : Int) (rows : List (List Int × Int))
    (nonempty : Int.ofNat shards.length>0) (ranks : Ranks shards)
    (valid : Int.ofNat shards.length=0 ∨ ∀ j : Int, (0≤j ∧ j<Int.ofNat dims.length) →
      0≤dims.getD j.toNat default ∧ dims.getD j.toNat default<Int.ofNat (shards.getD 0 default).shard_offsets.length)
    (hs : 0≤selected ∧ selected<Int.ofNat dims.length) (hd : d=Read dims selected)
    (hr : rows=(VeriPy.range 0 (Int.ofNat shards.length)).map (fun i=>(Key shards dims d i,i))) :
    _find_nd_overlapping_shards__inv_71 shards dims count selected d ((rows.mergeSort (fun a b=>VeriPy.lexInts a.1 b.1)).map Prod.snd) [] 0 := by
  subst rows
  have dimensions:=DimensionsAvailable shards dims nonempty valid
  have chosen : 0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length := by rw [hd];exact dimensions _ (ReadMember dims selected hs)
  exact ⟨OrderDomain shards dims d (by intro he; rw [he] at nonempty; contradiction) chosen (fun s h=>RanksMember shards s ranks h),ActiveEmpty _ _ _,ProcessedEmpty _ _⟩

theorem CursorRead [Inhabited α] (xs pre suf : List α) (cur : α) (k : Int)
    (cursor : xs=pre++cur::suf) (hi : k=Int.ofNat pre.length) :
    (0≤k ∧ k<Int.ofNat xs.length) ∧ Read xs k=cur := by
  have hb : 0≤k ∧ k<Int.ofNat xs.length := by
    rw [hi,cursor,List.length_append,List.length_cons]
    simp only [VeriPy.ofNat_cast,Int.natCast_add,Int.natCast_one]
    omega
  refine ⟨hb,?_⟩
  rw [ReadNonnegative xs k hb.1,hi,cursor]
  change (pre++cur::suf).getD pre.length default=cur
  simp [List.getD_eq_getElem?_getD]

theorem OrderCursor (shards : List ShardMetadata) (order pre suf : List Int) (d idx k : Int)
    (domain : SweepDomain shards order d) (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length) :
    (0≤idx ∧ idx<Int.ofNat shards.length) ∧
    (Read shards idx).shard_offsets.length=(Read shards idx).shard_sizes.length ∧
    (0≤d ∧ d<Int.ofNat (Read shards idx).shard_offsets.length) :=
  DomainMember shards order d idx domain (by rw [cursor];simp)

theorem NDOuterInvalidIndex (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (bad : ¬(0≤(if idx<0 then Int.ofNat shards.length+idx else idx) ∧
      (if idx<0 then Int.ofNat shards.length+idx else idx)<Int.ofNat shards.length)) : False := by
  have h:=(DomainMember shards order d idx inv.1 (by rw [cursor];simp)).1
  rw [if_neg (show ¬idx<0 by omega)] at bad
  exact bad h

theorem NDOuterInvalidOffset (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (bad : ¬(0≤(if d<0 then Int.ofNat (Read shards idx).shard_offsets.length+d else d) ∧
      (if d<0 then Int.ofNat (Read shards idx).shard_offsets.length+d else d)<Int.ofNat (Read shards idx).shard_offsets.length)) : False := by
  have h:=(DomainMember shards order d idx inv.1 (by rw [cursor];simp)).2.2
  rw [if_neg (show ¬d<0 by omega)] at bad
  exact bad h

theorem NDOuterInvalidSize (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (bad : ¬(0≤(if d<0 then Int.ofNat (Read shards idx).shard_sizes.length+d else d) ∧
      (if d<0 then Int.ofNat (Read shards idx).shard_sizes.length+d else d)<Int.ofNat (Read shards idx).shard_sizes.length)) : False := by
  have h:=(DomainMember shards order d idx inv.1 (by rw [cursor];simp)).2
  rw [if_neg (show ¬d<0 by have := h.2;omega)] at bad
  apply bad
  simpa only [h.1] using h.2

theorem PairResult (a b : ShardMetadata) (value : Bool)
    (ranks : a.shard_offsets.length=a.shard_sizes.length ∧ a.shard_sizes.length=b.shard_offsets.length ∧ b.shard_offsets.length=b.shard_sizes.length)
    (post : _check_shard_metadata_pair_overlap__post a b value) : value=true ↔ ShardsOverlap a b := by
  change (value=true ↔ ∀ j : Int, (0≤j ∧ j<Int.ofNat a.shard_offsets.length) →
    a.shard_offsets.getD j.toNat default < b.shard_offsets.getD j.toNat default+b.shard_sizes.getD j.toNat default ∧
    b.shard_offsets.getD j.toNat default < a.shard_offsets.getD j.toNat default+a.shard_sizes.getD j.toNat default) at post
  constructor
  · intro h
    refine ⟨ranks.1,ranks.2.2,ranks.1.trans ranks.2.1,?_⟩
    intro d hd
    simpa only [Read,if_neg (show ¬d<0 by omega)] using post.mp h d hd
  · intro h
    apply post.mpr
    intro d hd
    simpa only [Read,if_neg (show ¬d<0 by omega)] using h.2.2.2 d hd

theorem NDWitness (shards : List ShardMetadata) (dims : List Int) (a b : Int)
    (ha : 0≤a ∧ a<Int.ofNat shards.length) (hb : 0≤b ∧ b<Int.ofNat shards.length) (distinct : a≠b)
    (overlap : ShardsOverlap (Read shards a) (Read shards b)) :
    _find_nd_overlapping_shards__post shards dims (some (a,b)) := by
  have na : ¬a<0 := by omega
  have nb : ¬b<0 := by omega
  simp only [_find_nd_overlapping_shards__post,Option.getD_some,ne_eq,reduceCtorEq,not_false_eq_true,not_true_eq_false,false_or,true_or,and_true,if_neg na,if_neg nb]
  refine ⟨⟨ha,hb,distinct⟩,?_⟩
  rintro ⟨d,hd,separated⟩
  rw [ReadNonnegative shards a ha.1,ReadNonnegative shards b hb.1] at overlap
  have both:=overlap.2.2.2 d hd
  simp only [Read,if_neg (show ¬d<0 by omega)] at both
  omega

theorem EarlierDifferent (shards : List ShardMetadata) (order pre suf : List Int) (d idx k a : Int)
    (domain : SweepDomain shards order d) (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length)
    (earlier : a∈order.take k.toNat) : a≠idx := by
  have later : idx∈order.drop k.toNat := by
    rw [hi,cursor]
    change idx∈(pre++idx::suf).drop pre.length
    simp
  exact (domain.2.2.2.2.rel_of_mem_take_of_mem_drop earlier later).1

theorem ActivePairRanks (shards : List ShardMetadata) (order : List Int) (d k idx : Int) (active : List (Int × Int)) (row : Int × Int)
    (domain : SweepDomain shards order d) (state : ActiveState shards order k d active)
    (idxMember : idx∈order) (rowMember : row∈active) :
    (Read shards idx).shard_offsets.length=(Read shards idx).shard_sizes.length ∧
    (Read shards idx).shard_sizes.length=(Read shards row.2).shard_offsets.length ∧
    (Read shards row.2).shard_offsets.length=(Read shards row.2).shard_sizes.length := by
  have a:=DomainMember shards order d idx domain idxMember
  have b:=state.2.1 row rowMember
  have ra:=domain.2.2.1 _ (ReadMember shards idx a.1)
  have rb:=domain.2.2.1 _ (ReadMember shards row.2 b.1)
  exact ⟨ra.1,ra.1.symm.trans (ra.2.trans rb.2.symm),rb.1⟩

theorem NDCallSafety (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k cut : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (innerCursor : active.drop cut.toNat=innerPre++row::innerSuf) :
    (Read shards idx).shard_offsets.length=(Read shards idx).shard_sizes.length ∧
    (Read shards idx).shard_sizes.length=(Read shards row.2).shard_offsets.length ∧
    (Read shards row.2).shard_offsets.length=(Read shards row.2).shard_sizes.length := by
  apply ActivePairRanks shards order d k idx active row inv.1 inv.2.1
  · rw [cursor];simp
  · apply List.mem_of_mem_drop (i := cut.toNat)
    rw [innerCursor];simp

theorem NDCallRank0 (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (innerCursor : active.drop cut=innerPre++row::innerSuf) :
    Int.ofNat (Read shards idx).shard_offsets.length=Int.ofNat (Read shards idx).shard_sizes.length := by
  exact congrArg Int.ofNat (NDCallSafety shards dims order pre suf count selected d idx k (Int.ofNat cut) active innerPre innerSuf row inv cursor innerCursor).1

theorem NDCallRank1 (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (innerCursor : active.drop cut=innerPre++row::innerSuf) :
    Int.ofNat (Read shards idx).shard_sizes.length=Int.ofNat (Read shards row.2).shard_offsets.length := by
  exact congrArg Int.ofNat (NDCallSafety shards dims order pre suf count selected d idx k (Int.ofNat cut) active innerPre innerSuf row inv cursor innerCursor).2.1

theorem NDCallRank2 (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (innerCursor : active.drop cut=innerPre++row::innerSuf) :
    Int.ofNat (Read shards row.2).shard_offsets.length=Int.ofNat (Read shards row.2).shard_sizes.length := by
  exact congrArg Int.ofNat (NDCallSafety shards dims order pre suf count selected d idx k (Int.ofNat cut) active innerPre innerSuf row inv cursor innerCursor).2.2

theorem NDInnerIndexSafe (shards : List ShardMetadata) (dims order : List Int)
    (count selected d k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (innerCursor : active.drop cut=innerPre++row::innerSuf)
    (bad : ¬(0≤(if row.2<0 then Int.ofNat shards.length+row.2 else row.2) ∧
      (if row.2<0 then Int.ofNat shards.length+row.2 else row.2)<Int.ofNat shards.length)) : False := by
  have member : row∈active := by apply List.mem_of_mem_drop (i := cut);rw [innerCursor];simp
  have h:=(inv.2.1.2.1 row member).1
  rw [if_neg (show ¬row.2<0 by omega)] at bad
  exact bad h

theorem PairFalse (a b : ShardMetadata) (value : Bool)
    (post : _check_shard_metadata_pair_overlap__post a b value) (no : ¬value=true) : ¬ShardsOverlap a b := by
  intro h
  apply no
  apply post.mpr
  intro d hd
  simpa only [Read,if_neg (show ¬d<0 by omega)] using h.2.2.2 d hd

theorem NDScannedStep (shards : List ShardMetadata) (dims : List Int) (count selected d : Int) (order : List Int)
    (active pre suf : List (Int × Int)) (outer idx : Int) (current : ShardMetadata) (start ending cutoff k : Int)
    (row : Int × Int) (value : Bool)
    (inv : _find_nd_overlapping_shards__inv_84 shards dims count selected d order active outer idx current start ending cutoff k)
    (cursor : active=pre++row::suf) (hi : k=Int.ofNat pre.length)
    (post : _check_shard_metadata_pair_overlap__post (Read shards idx) (Read shards row.2) value)
    (no : ¬value=true) :
    _find_nd_overlapping_shards__inv_84 shards dims count selected d order active outer idx current start ending cutoff (k+1) := by
  have read:=CursorRead active pre suf row k cursor hi
  apply ScannedStep shards idx k active read.1 inv
  rw [read.2]
  exact PairFalse _ _ value post no

theorem NDCurrentRank (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) :
    Int.ofNat (Read shards idx).shard_offsets.length=Int.ofNat (Read shards idx).shard_sizes.length := by
  exact congrArg Int.ofNat (DomainMember shards order d idx inv.1 (by rw [cursor];simp)).2.1

theorem NDCallRank1Plain (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (innerCursor : active=innerPre++row::innerSuf) :
    Int.ofNat (Read shards idx).shard_sizes.length=Int.ofNat (Read shards row.2).shard_offsets.length :=
  NDCallRank1 shards dims order pre suf count selected d idx k 0 active innerPre innerSuf row inv cursor innerCursor

theorem NDCallRank2Plain (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (innerCursor : active=innerPre++row::innerSuf) :
    Int.ofNat (Read shards row.2).shard_offsets.length=Int.ofNat (Read shards row.2).shard_sizes.length :=
  NDCallRank2 shards dims order pre suf count selected d idx k 0 active innerPre innerSuf row inv cursor innerCursor

theorem NDInnerIndexSafePlain (shards : List ShardMetadata) (dims order : List Int)
    (count selected d k : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (innerCursor : active=innerPre++row::innerSuf)
    (bad : ¬(0≤(if row.2<0 then Int.ofNat shards.length+row.2 else row.2) ∧
      (if row.2<0 then Int.ofNat shards.length+row.2 else row.2)<Int.ofNat shards.length)) : False :=
  NDInnerIndexSafe shards dims order count selected d k 0 active innerPre innerSuf row inv innerCursor bad

theorem NDFound (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int) (value : Bool)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length)
    (innerCursor : active.drop cut=innerPre++row::innerSuf)
    (post : _check_shard_metadata_pair_overlap__post (Read shards idx) (Read shards row.2) value)
    (yes : value=true) :
    ∃ a, some (row.2,idx)=a ∧ _find_nd_overlapping_shards__post shards dims a := by
  have rowMember : row∈active := by apply List.mem_of_mem_drop (i := cut);rw [innerCursor];simp
  have idxMember : idx∈order := by rw [cursor];simp
  have ranks:=ActivePairRanks shards order d k idx active row inv.1 inv.2.1 idxMember rowMember
  have overlapping:=(PairResult _ _ value ranks post).mp yes
  have a:=(inv.2.1.2.1 row rowMember)
  have b:=(DomainMember shards order d idx inv.1 idxMember).1
  have different:=EarlierDifferent shards order pre suf d idx k row.2 inv.1 cursor hi a.2.1
  exact ⟨_,rfl,NDWitness shards dims row.2 idx a.1 b different ((OverlapSymmetric _ _).mp overlapping)⟩

theorem NDFoundPlain (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int) (value : Bool)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length)
    (innerCursor : active=innerPre++row::innerSuf)
    (post : _check_shard_metadata_pair_overlap__post (Read shards idx) (Read shards row.2) value)
    (yes : value=true) :
    ∃ a, some (row.2,idx)=a ∧ _find_nd_overlapping_shards__post shards dims a :=
  NDFound shards dims order pre suf count selected d idx k 0 active innerPre innerSuf row value inv cursor hi innerCursor post yes

theorem ReturnFromLoop {α : Type} (returned : Option α) (value : α) (Q : α → Prop) (C : Prop)
    (h : returned=none ∧ C ∨ ∃ a, returned=some a ∧ Q a)
    (done : returned=some value) : Q value := by
  rcases h with ⟨he,_⟩ | ⟨a,ha,post⟩
  · rw [done] at he;contradiction
  · have eq : value=a := Option.some.inj (done.symm.trans ha)
    simpa only [eq] using post

theorem ReturnExists {α : Type} (returned : Option α) (value : α) (Q : α → Prop) (C : Prop)
    (h : returned=none ∧ C ∨ ∃ a, returned=some a ∧ Q a)
    (done : returned=some value) : ∃ a,value=a ∧ Q a :=
  ⟨value,rfl,ReturnFromLoop returned value Q C h done⟩

theorem NDOuterStepDrop (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k inner : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length)
    (scan : Scanned shards idx (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807))) inner)
    (done : inner=Int.ofNat (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807))).length) :
    _find_nd_overlapping_shards__inv_71 shards dims count selected d order
      (VeriPy.insort ActiveLex (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807))) (End shards d idx,idx)) (k+1) := by
  have read:=CursorRead order pre suf idx k cursor hi
  have dropped:=ActiveSuffix shards order k d active inv.2.1
  rw [read.2] at dropped
  have complete : Scanned shards (Read order k)
      (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807)))
      (Int.ofNat (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807))).length) := by
    rw [read.2];rw [done] at scan;exact scan
  have disjoint:=SweepStep shards order k d _ inv.1 dropped inv.2.2 complete read.1.2
  have inserted:=ActiveInsert shards order k d _ inv.1 dropped read.1.2
  rw [read.2] at inserted
  exact ⟨inv.1,inserted,disjoint⟩

theorem NDOuterStepPlain (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k inner : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length)
    (scan : Scanned shards idx active inner) (done : inner=Int.ofNat active.length)
    (zero : VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807)=0) :
    _find_nd_overlapping_shards__inv_71 shards dims count selected d order
      (VeriPy.insort ActiveLex active (End shards d idx,idx)) (k+1) := by
  have read:=CursorRead order pre suf idx k cursor hi
  have dropped:=ActiveSuffix shards order k d active inv.2.1
  rw [read.2,zero,List.drop_zero] at dropped
  have complete : Scanned shards (Read order k) active (Int.ofNat active.length) := by
    rw [read.2];rw [done] at scan;exact scan
  have disjoint:=SweepStep shards order k d active inv.1 dropped inv.2.2 complete read.1.2
  have inserted:=ActiveInsert shards order k d active inv.1 dropped read.1.2
  rw [read.2] at inserted
  exact ⟨inv.1,inserted,disjoint⟩

theorem NDFinish (shards : List ShardMetadata) (dims order : List Int)
    (count selected d k : Int) (active : List (Int × Int))
    (ranks : Ranks shards)
    (inv : _find_nd_overlapping_shards__inv_71 shards dims count selected d order active k)
    (done : k=Int.ofNat order.length) : _find_nd_overlapping_shards__post shards dims none := by
  have processed:=inv.2.2
  rw [done] at processed
  exact SearchComplete shards dims order d ranks inv.1 processed

-- Checked function proofs; these refer to the unchanged generated models.
@[spec]
theorem _check_shard_metadata_pair_overlap__proof («shard1» : «ShardMetadata») («shard2» : «ShardMetadata») (__vp_h0 : (((Int.ofNat ((«shard1»).«shard_offsets»).length) = (Int.ofNat ((«shard1»).«shard_sizes»).length)) ∧ ((Int.ofNat ((«shard1»).«shard_sizes»).length) = (Int.ofNat ((«shard2»).«shard_offsets»).length)) ∧ ((Int.ofNat ((«shard2»).«shard_offsets»).length) = (Int.ofNat ((«shard2»).«shard_sizes»).length)))) :
  ⦃⌜True⌝⦄ «_check_shard_metadata_pair_overlap» «shard1» «shard2» ⦃(fun __vp_result => ⌜(«_check_shard_metadata_pair_overlap__post» «shard1» «shard2» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_check_shard_metadata_pair_overlap__error» «shard1» «shard2» __vp_error)⌝, ())⦄ := by
  mvcgen [«_check_shard_metadata_pair_overlap», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 22; exact (by (first | veripy_capture «ndims» | veripy_let «ndims» := (Int.ofNat ((«shard1»).«shard_offsets»).length) | veripy_capture_type «ndims» : Int); exact Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜«_check_shard_metadata_pair_overlap__post» «shard1» «shard2» __vp_return⌝) (onContinue := fun __vp_cursor «__vp_index_22» => ⌜(«_check_shard_metadata_pair_overlap__inv_22» «shard1» «shard2» «ndims» «__vp_index_22») ∧ «__vp_index_22» = Int.ofNat __vp_cursor.prefix.length⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)))
  all_goals (
    try veripy_clear_aux
    try (simp only [VeriPy.loopTag, decide_eq_true_eq, WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals try veripy_continue_facts
    all_goals try veripy_project_facts
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals try veripy_fold_projections
    all_goals try (simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.not_ofNat_neg, if_false, Int.toNat_natCast] at *)
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «ActiveEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveInsert» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActivePairRanks» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveSuffix» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AllPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAfter» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAuxFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectBefore» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BuildKey» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedMap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CursorRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsAvailable» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsFromIndices» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DomainMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «EarlierDifferent» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortMembers» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortOrdered» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexHead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidOffset» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidSize» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFoundPlain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDMapRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderDomain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderPerm» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderReadNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderStarts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OverlapSymmetric» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairFalse» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairResult» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStepCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ProcessedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeDistinct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeFailure» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeLength» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RanksMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadNonnegative» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnExists» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnFromLoop» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchOverlapWitness» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SelectedDimension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SeparatedExpired» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SweepStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TakeNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «ActiveEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveInsert» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActivePairRanks» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveSuffix» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AllPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAfter» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAuxFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectBefore» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BuildKey» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedMap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CursorRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsAvailable» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsFromIndices» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DomainMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «EarlierDifferent» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortMembers» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortOrdered» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexHead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidOffset» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidSize» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFoundPlain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDMapRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderDomain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderPerm» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderReadNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderStarts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OverlapSymmetric» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairFalse» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairResult» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStepCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ProcessedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeDistinct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeFailure» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeLength» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RanksMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadNonnegative» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnExists» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnFromLoop» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchOverlapWitness» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SelectedDimension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SeparatedExpired» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SweepStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TakeNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«_check_shard_metadata_pair_overlap__post», «_check_shard_metadata_pair_overlap__error»] | grind [«NDFound», «NDFoundPlain», «NDScannedStep», «PairFalse», «PairInit», «PairPost», «PairResult», «PairStep», «PairStepCursor», «_check_shard_metadata_pair_overlap__inv_22», «_check_shard_metadata_pair_overlap__post», «_check_shard_metadata_pair_overlap__error»] | grind (lax := true) [«ActiveEmpty», «ActiveInsert», «ActivePairRanks», «ActiveSuffix», «ActiveTotal», «ActiveTrans», «AllPairs», «BisectAfter», «BisectAuxFacts», «BisectBefore», «BisectFacts», «BuildKey», «CheckedMap», «CheckedRead», «CursorRead», «DimensionCursor», «DimensionsAvailable», «DimensionsFromIndices», «DomainMember», «EarlierDifferent», «InsortMembers», «InsortOrdered», «LexHead», «LexIntsTotal», «LexIntsTrans», «NDChooseInvalidOffset», «NDChooseInvalidSize», «NDFound», «NDFoundPlain», «NDMapRows», «NDScannedStep», «OrderCursor», «OrderDomain», «OrderPerm», «OrderReadNext», «OrderStarts», «OverlapSymmetric», «PairFalse», «PairInit», «PairPost», «PairResult», «PairStep», «PairStepCursor», «ProcessedEmpty», «RangeCursor», «RangeDistinct», «RangeFailure», «RangeLength», «RangeMember», «RanksMember», «ReadMember», «ReadNonnegative», «ReturnExists», «ReturnFromLoop», «ScannedEmpty», «ScannedStep», «SearchOverlapWitness», «SelectedDimension», «SeparatedExpired», «SweepStep», «TakeNext», «_check_shard_metadata_pair_overlap__inv_22», «_check_shard_metadata_pair_overlap__post», «_check_shard_metadata_pair_overlap__error»]
  )

theorem NDZero (n : Nat) (h : ¬ (n : Int) ≠ 0) : n=0 := by omega
@[spec]
theorem _find_nd_overlapping_shards__proof («shards» : (List «ShardMetadata»)) («sharded_dims» : (List Int)) (__vp_h0 : (((Int.ofNat («shards»).length) ≤ (9223372036854775807 : Int)))) (__vp_h1 : ((((Int.ofNat («shards»).length) ≤ (1 : Int))) ∨ (((Int.ofNat («sharded_dims»).length) > (0 : Int))))) (__vp_h2 : (∀ «a» : Int, (0 ≤ «a» ∧ «a» < (Int.ofNat («shards»).length)) → ((((Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_offsets»).length) = (Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_sizes»).length))) ∧ (((Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_offsets»).length) = (Int.ofNat ((((«shards»).getD ((0 : Int)).toNat default)).«shard_offsets»).length)))))) (__vp_h3 : (∀ «a» : Int, (0 ≤ «a» ∧ «a» < (Int.ofNat («shards»).length)) → (∀ «k» : Int, (0 ≤ «k» ∧ «k» < (Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_sizes»).length)) → (((((((«shards»).getD («a»).toNat default)).«shard_sizes»).getD («k»).toNat default) > (0 : Int)))))) (__vp_h4 : ((((Int.ofNat («shards»).length) = (0 : Int))) ∨ (∀ «k» : Int, (0 ≤ «k» ∧ «k» < (Int.ofNat («sharded_dims»).length)) → (((0 : Int) ≤ ((«sharded_dims»).getD («k»).toNat default)) ∧ (((«sharded_dims»).getD («k»).toNat default) < (Int.ofNat ((((«shards»).getD ((0 : Int)).toNat default)).«shard_offsets»).length)))))) :
  ⦃⌜True⌝⦄ «_find_nd_overlapping_shards» «shards» «sharded_dims» ⦃(fun __vp_result => ⌜(«_find_nd_overlapping_shards__post» «shards» «sharded_dims» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_find_nd_overlapping_shards__error» «shards» «sharded_dims» __vp_error)⌝, ())⦄ := by
  mvcgen [«_find_nd_overlapping_shards», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 53; exact (by (first | veripy_capture «dims» | veripy_let «dims» := (Int.ofNat («sharded_dims»).length) | veripy_capture_type «dims» : Int); exact ⇓⟨__vp_cursor, «sweep_dim_idx», «max_size», «__vp_index_53»⟩ => ⌜(«_find_nd_overlapping_shards__inv_53» «shards» «sharded_dims» «dims» «sweep_dim_idx» «max_size» «__vp_index_53») ∧ «__vp_index_53» = Int.ofNat __vp_cursor.prefix.length⌝))
  all_goals try (veripy_loop_tag 71; exact (by (first | veripy_capture «dims» | veripy_let «dims» := (Int.ofNat («sharded_dims»).length) | veripy_capture_type «dims» : Int); (first | veripy_capture «sweep_dim_idx» | veripy_let «sweep_dim_idx» := (0 : Int) | veripy_capture_type «sweep_dim_idx» : Int); (first | veripy_capture «sweep_dim» | veripy_let «sweep_dim» := ((«sharded_dims»).getD ((if «sweep_dim_idx» < 0 then Int.ofNat («sharded_dims»).length + «sweep_dim_idx» else «sweep_dim_idx»)).toNat default) | veripy_capture_type «sweep_dim» : Int); (first | veripy_capture «sorted_indices» | veripy_let «sorted_indices» := ((((VeriPy.range 0 (Int.ofNat («shards»).length))).map (fun «idx» => (([(((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «sweep_dim» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «sweep_dim» else «sweep_dim»)).toNat default)] ++ (((«sharded_dims»).filter (fun «d» => decide (((«d» ≠ «sweep_dim»))))).map (fun «d» => (((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «d» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «d» else «d»)).toNat default)))), «idx»))).mergeSort (fun a b => VeriPy.lexInts a.1 b.1)).map Prod.snd | veripy_capture_type «sorted_indices» : (List Int)); exact Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜«_find_nd_overlapping_shards__post» «shards» «sharded_dims» __vp_return⌝) (onContinue := fun __vp_cursor («active», «__vp_index_71») => ⌜(«_find_nd_overlapping_shards__inv_71» «shards» «sharded_dims» «dims» «sweep_dim_idx» «sweep_dim» «sorted_indices» «active» «__vp_index_71») ∧ «__vp_index_71» = Int.ofNat __vp_cursor.prefix.length⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)))
  all_goals try (veripy_loop_tag 84; exact (by (first | veripy_capture «dims» | veripy_let «dims» := (Int.ofNat («sharded_dims»).length) | veripy_capture_type «dims» : Int); (first | veripy_capture «sweep_dim_idx» | veripy_let «sweep_dim_idx» := (0 : Int) | veripy_capture_type «sweep_dim_idx» : Int); (first | veripy_capture «sweep_dim» | veripy_let «sweep_dim» := ((«sharded_dims»).getD ((if «sweep_dim_idx» < 0 then Int.ofNat («sharded_dims»).length + «sweep_dim_idx» else «sweep_dim_idx»)).toNat default) | veripy_capture_type «sweep_dim» : Int); (first | veripy_capture «sorted_indices» | veripy_let «sorted_indices» := ((((VeriPy.range 0 (Int.ofNat («shards»).length))).map (fun «idx» => (([(((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «sweep_dim» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «sweep_dim» else «sweep_dim»)).toNat default)] ++ (((«sharded_dims»).filter (fun «d» => decide (((«d» ≠ «sweep_dim»))))).map (fun «d» => (((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «d» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «d» else «d»)).toNat default)))), «idx»))).mergeSort (fun a b => VeriPy.lexInts a.1 b.1)).map Prod.snd | veripy_capture_type «sorted_indices» : (List Int)); (first | veripy_capture «active» | veripy_let «active» := [] | veripy_capture_type «active» : (List (Int × Int))); (first | veripy_capture «__vp_index_71» | veripy_capture_type «__vp_index_71» : Int); (first | veripy_capture «idx» | veripy_cursor «idx» 71 0 0 0 | veripy_capture_type «idx» : Int); (first | veripy_capture «current» | veripy_let «current» := ((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default) | veripy_capture_type «current» : «ShardMetadata»); (first | veripy_capture «start» | veripy_let «start» := (((«current»).«shard_offsets»).getD ((if «sweep_dim» < 0 then Int.ofNat ((«current»).«shard_offsets»).length + «sweep_dim» else «sweep_dim»)).toNat default) | veripy_capture_type «start» : Int); (first | veripy_capture «end» | veripy_let «end» := («start» + (((«current»).«shard_sizes»).getD ((if «sweep_dim» < 0 then Int.ofNat ((«current»).«shard_sizes»).length + «sweep_dim» else «sweep_dim»)).toNat default)) | veripy_capture_type «end» : Int); (first | veripy_capture «cutoff» | veripy_let «cutoff» := (Int.ofNat (VeriPy.bisectRight (fun a b => decide ((a).1 < (b).1 ∨ ((a).1 = (b).1 ∧ ((a).2 ≤ (b).2)))) «active» («start», (9223372036854775807 : Int)))) | veripy_capture_type «cutoff» : Int); exact Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜«_find_nd_overlapping_shards__post» «shards» «sharded_dims» __vp_return⌝) (onContinue := fun __vp_cursor «__vp_index_84» => ⌜(«_find_nd_overlapping_shards__inv_84» «shards» «sharded_dims» «dims» «sweep_dim_idx» «sweep_dim» «sorted_indices» «active» «__vp_index_71» «idx» «current» «start» «end» «cutoff» «__vp_index_84») ∧ «__vp_index_84» = Int.ofNat __vp_cursor.prefix.length⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)))
  all_goals (
    try veripy_clear_aux
    try (simp only [VeriPy.loopTag, decide_eq_true_eq, WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals try veripy_continue_facts
    all_goals try veripy_project_facts
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals try veripy_fold_projections
    all_goals try (simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.not_ofNat_neg, if_false, Int.toNat_natCast] at *)
    all_goals try (first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega)
  )
  try (case' vc1.isTrue => solve | apply SearchTrivial <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc3.step.isTrue.isTrue.isTrue.isTrue.isTrue.left => solve | apply NDChooseStep <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc5.step.isTrue.isTrue.isTrue.isFalse => solve | apply NDChooseInvalidSize <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc7.step.isTrue.isFalse => solve | apply NDChooseInvalidOffset <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc9.isFalse.isFalse.isTrue.pre.left => solve | apply NDChooseInit <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc10.h => solve | apply NDMapRows <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc11.__vp_h0.left => solve | apply NDCurrentRank <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc11.__vp_h0.right.left => solve | apply NDCallRank1 <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc11.__vp_h0.right.right => solve | apply NDCallRank2 <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc12.step.isTrue.success.isTrue => solve | apply NDFound <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc13.step.isTrue.success.isFalse.left => solve | apply NDScannedStep <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc14.step.isFalse => solve | apply NDInnerIndexSafe <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc15.step.isTrue.isTrue.isTrue.isTrue.pre.left => solve | apply NDInnerInit <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc16.step.isTrue.isTrue.isTrue.isTrue.post.success.h_1 => solve | apply ReturnExists <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc17.step.isTrue.isTrue.isTrue.isTrue.post.success.h_2.left => solve | apply NDOuterStepDrop <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc19.__vp_h0.left => solve | apply NDCurrentRank <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc19.__vp_h0.right.left => solve | apply NDCallRank1Plain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc19.__vp_h0.right.right => solve | apply NDCallRank2Plain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc20.step.isTrue.success.isTrue => solve | apply NDFoundPlain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc21.step.isTrue.success.isFalse.left => solve | apply NDScannedStep <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc22.step.isFalse => solve | apply NDInnerIndexSafePlain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc23.step.isTrue.isTrue.isTrue.isFalse.pre.left => solve | apply NDInnerInit <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc24.step.isTrue.isTrue.isTrue.isFalse.post.success.h_1 => solve | apply ReturnExists <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc25.step.isTrue.isTrue.isTrue.isFalse.post.success.h_2.left => solve | apply NDOuterStepPlain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc27.step.isTrue.isTrue.isFalse => solve | apply NDOuterInvalidSize <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc28.step.isTrue.isFalse => solve | apply NDOuterInvalidOffset <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc29.step.isFalse => solve | apply NDOuterInvalidIndex <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc30.isFalse.isFalse.isTrue.post.success.isTrue.success.pre.left => solve | apply NDOuterInit <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc31.isFalse.isFalse.isTrue.post.success.isTrue.success.post.success.h_1 => solve | apply ReturnFromLoop <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc32.isFalse.isFalse.isTrue.post.success.isTrue.success.post.success.h_2 => solve | apply NDFinish <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc36.h => solve | apply NDMapRows <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc37.__vp_h0.left => solve | apply NDCurrentRank <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc37.__vp_h0.right.left => solve | apply NDCallRank1 <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc37.__vp_h0.right.right => solve | apply NDCallRank2 <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc38.step.isTrue.success.isTrue => solve | apply NDFound <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc39.step.isTrue.success.isFalse.left => solve | apply NDScannedStep <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc40.step.isFalse => solve | apply NDInnerIndexSafe <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc41.step.isTrue.isTrue.isTrue.isTrue.pre.left => solve | apply NDInnerInit <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc42.step.isTrue.isTrue.isTrue.isTrue.post.success.h_1 => solve | apply ReturnExists <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc43.step.isTrue.isTrue.isTrue.isTrue.post.success.h_2.left => solve | apply NDOuterStepDrop <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc45.__vp_h0.left => solve | apply NDCurrentRank <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc45.__vp_h0.right.left => solve | apply NDCallRank1Plain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc45.__vp_h0.right.right => solve | apply NDCallRank2Plain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc46.step.isTrue.success.isTrue => solve | apply NDFoundPlain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc47.step.isTrue.success.isFalse.left => solve | apply NDScannedStep <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc48.step.isFalse => solve | apply NDInnerIndexSafePlain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc49.step.isTrue.isTrue.isTrue.isFalse.pre.left => solve | apply NDInnerInit <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc50.step.isTrue.isTrue.isTrue.isFalse.post.success.h_1 => solve | apply ReturnExists <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc51.step.isTrue.isTrue.isTrue.isFalse.post.success.h_2.left => solve | apply NDOuterStepPlain <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc53.step.isTrue.isTrue.isFalse => solve | apply NDOuterInvalidSize <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc54.step.isTrue.isFalse => solve | apply NDOuterInvalidOffset <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc55.step.isFalse => solve | apply NDOuterInvalidIndex <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc56.isFalse.isFalse.isFalse.isTrue.success.pre.left => solve | apply NDOuterInit <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc57.isFalse.isFalse.isFalse.isTrue.success.post.success.h_1 => solve | apply ReturnFromLoop <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)
  try (case' vc58.isFalse.isFalse.isFalse.isTrue.success.post.success.h_2 => solve | apply NDFinish <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false, Int.not_ofNat_neg, Int.toNat_natCast]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)

  case' vc36.h =>
    apply NDMapRows shards sharded_dims 0
    · simp only [VeriPy.ofNat_cast]; omega
    · intro a ha; exact __vp_h2 a ha.1 ha.2
    · rcases __vp_h4 with h | h
      · exact Or.inl h
      · exact Or.inr (fun k hk => h k hk.1 hk.2)
    · simp only [VeriPy.ofNat_cast]; omega

  case' vc25.step.isTrue.isTrue.isTrue.isFalse.post.success.h_2.left =>
    apply NDOuterStepPlain
    all_goals try assumption
    all_goals first | (apply NDZero; assumption) | (simp only [VeriPy.ofNat_cast, ActiveLex, Start, Read]; omega)
  case' vc51.step.isTrue.isTrue.isTrue.isFalse.post.success.h_2.left =>
    apply NDOuterStepPlain
    all_goals try assumption
    all_goals first | (apply NDZero; assumption) | (simp only [VeriPy.ofNat_cast, ActiveLex, Start, Read]; omega)

