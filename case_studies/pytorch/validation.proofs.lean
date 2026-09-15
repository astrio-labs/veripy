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


def Partitioned (shards : List ShardMetadata) (dims : List Int) (upto : Int) : Prop :=
  (∀ k : Int, 0≤k ∧ k<Int.ofNat dims.length → 0≤Read dims k ∧ Read dims k<upto) ∧
  (∀ d : Int, 0≤d ∧ d<upto → d∉dims → ∀ a : Int, 0≤a ∧ a<Int.ofNat shards.length →
    Read (Read shards a).shard_offsets d=Read (Read shards 0).shard_offsets d ∧
    Read (Read shards a).shard_sizes d=Read (Read shards 0).shard_sizes d)
def SamePrefix (shards : List ShardMetadata) (d k : Int) : Prop :=
  ∀ a : Int, 0≤a ∧ a<k →
    Read (Read shards a).shard_offsets d=Read (Read shards 0).shard_offsets d ∧
    Read (Read shards a).shard_sizes d=Read (Read shards 0).shard_sizes d

-- VERIPY PRELUDE END



theorem PairInit (a b : ShardMetadata) (n : Int) :
    _check_shard_metadata_pair_overlap__inv_23 a b n 0 := by
  unfold _check_shard_metadata_pair_overlap__inv_23
  intro j hj; omega

theorem PairStep (a b : ShardMetadata) (n i : Int)
    (h : _check_shard_metadata_pair_overlap__inv_23 a b n i)
    (left : ¬ a.shard_offsets.getD i.toNat default ≥ b.shard_offsets.getD i.toNat default + b.shard_sizes.getD i.toNat default)
    (right : ¬ b.shard_offsets.getD i.toNat default ≥ a.shard_offsets.getD i.toNat default + a.shard_sizes.getD i.toNat default) :
    _check_shard_metadata_pair_overlap__inv_23 a b n (i+1) := by
  intro j hj
  by_cases he : j = i
  · subst j; constructor <;> omega
  · exact h j (by omega)

theorem PairPost (a b : ShardMetadata) (n : Int)
    (h : _check_shard_metadata_pair_overlap__inv_23 a b n (Int.ofNat a.shard_offsets.length)) :
    _check_shard_metadata_pair_overlap__post a b true := by
  unfold _check_shard_metadata_pair_overlap__post
  constructor
  · intro _; simpa only [_check_shard_metadata_pair_overlap__inv_23, Int.zero_add] using h
  · intro _; rfl


theorem RangeLength (n : Nat) : (VeriPy.range 0 (Int.ofNat n)).length = n := by
  simp [VeriPy.range]

theorem PairStepCursor (a b : ShardMetadata) (n cur i : Int) (pre suf : List Int)
    (hr : VeriPy.range 0 n = pre ++ cur :: suf) (hi : i = Int.ofNat pre.length)
    (h : _check_shard_metadata_pair_overlap__inv_23 a b n i)
    (left : ¬ a.shard_offsets.getD cur.toNat default ≥ b.shard_offsets.getD cur.toNat default + b.shard_sizes.getD cur.toNat default)
    (right : ¬ b.shard_offsets.getD cur.toNat default ≥ a.shard_offsets.getD cur.toNat default + a.shard_sizes.getD cur.toNat default) :
    _check_shard_metadata_pair_overlap__inv_23 a b n (i+1) := by
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
    _find_nd_overlapping_shards__inv_54 shards dims count 0 0 0 := by
  exact ⟨by omega,positive⟩

theorem NDChooseStep (shards : List ShardMetadata) (dims pre suf : List Int) (count maximum i cur : Int)
    (cursor : dims=pre++cur::suf) (hi : i=Int.ofNat pre.length) :
    _find_nd_overlapping_shards__inv_54 shards dims count i maximum (i+1) := by
  constructor
  · rw [hi];exact Int.natCast_nonneg _
  · rw [hi,cursor,List.length_append,List.length_cons]
    simp only [VeriPy.ofNat_cast,Int.natCast_add,Int.natCast_one]
    omega

theorem NDInnerInit (shards : List ShardMetadata) (dims : List Int) (count selected d : Int) (order : List Int)
    (active : List (Int × Int)) (outer idx : Int) (current : ShardMetadata) (start ending cutoff : Int) :
    _find_nd_overlapping_shards__inv_85 shards dims count selected d order active outer idx current start ending cutoff 0 :=
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
    _find_nd_overlapping_shards__inv_72 shards dims count selected d ((rows.mergeSort (fun a b=>VeriPy.lexInts a.1 b.1)).map Prod.snd) [] 0 := by
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
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (bad : ¬(0≤(if idx<0 then Int.ofNat shards.length+idx else idx) ∧
      (if idx<0 then Int.ofNat shards.length+idx else idx)<Int.ofNat shards.length)) : False := by
  have h:=(DomainMember shards order d idx inv.1 (by rw [cursor];simp)).1
  rw [if_neg (show ¬idx<0 by omega)] at bad
  exact bad h

theorem NDOuterInvalidOffset (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (bad : ¬(0≤(if d<0 then Int.ofNat (Read shards idx).shard_offsets.length+d else d) ∧
      (if d<0 then Int.ofNat (Read shards idx).shard_offsets.length+d else d)<Int.ofNat (Read shards idx).shard_offsets.length)) : False := by
  have h:=(DomainMember shards order d idx inv.1 (by rw [cursor];simp)).2.2
  rw [if_neg (show ¬d<0 by omega)] at bad
  exact bad h

theorem NDOuterInvalidSize (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
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
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
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
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (innerCursor : active.drop cut=innerPre++row::innerSuf) :
    Int.ofNat (Read shards idx).shard_offsets.length=Int.ofNat (Read shards idx).shard_sizes.length := by
  exact congrArg Int.ofNat (NDCallSafety shards dims order pre suf count selected d idx k (Int.ofNat cut) active innerPre innerSuf row inv cursor innerCursor).1

theorem NDCallRank1 (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (innerCursor : active.drop cut=innerPre++row::innerSuf) :
    Int.ofNat (Read shards idx).shard_sizes.length=Int.ofNat (Read shards row.2).shard_offsets.length := by
  exact congrArg Int.ofNat (NDCallSafety shards dims order pre suf count selected d idx k (Int.ofNat cut) active innerPre innerSuf row inv cursor innerCursor).2.1

theorem NDCallRank2 (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf)
    (innerCursor : active.drop cut=innerPre++row::innerSuf) :
    Int.ofNat (Read shards row.2).shard_offsets.length=Int.ofNat (Read shards row.2).shard_sizes.length := by
  exact congrArg Int.ofNat (NDCallSafety shards dims order pre suf count selected d idx k (Int.ofNat cut) active innerPre innerSuf row inv cursor innerCursor).2.2

theorem NDInnerIndexSafe (shards : List ShardMetadata) (dims order : List Int)
    (count selected d k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
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
    (inv : _find_nd_overlapping_shards__inv_85 shards dims count selected d order active outer idx current start ending cutoff k)
    (cursor : active=pre++row::suf) (hi : k=Int.ofNat pre.length)
    (post : _check_shard_metadata_pair_overlap__post (Read shards idx) (Read shards row.2) value)
    (no : ¬value=true) :
    _find_nd_overlapping_shards__inv_85 shards dims count selected d order active outer idx current start ending cutoff (k+1) := by
  have read:=CursorRead active pre suf row k cursor hi
  apply ScannedStep shards idx k active read.1 inv
  rw [read.2]
  exact PairFalse _ _ value post no

theorem NDCurrentRank (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active : List (Int × Int))
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) :
    Int.ofNat (Read shards idx).shard_offsets.length=Int.ofNat (Read shards idx).shard_sizes.length := by
  exact congrArg Int.ofNat (DomainMember shards order d idx inv.1 (by rw [cursor];simp)).2.1

theorem NDCallRank1Plain (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (innerCursor : active=innerPre++row::innerSuf) :
    Int.ofNat (Read shards idx).shard_sizes.length=Int.ofNat (Read shards row.2).shard_offsets.length :=
  NDCallRank1 shards dims order pre suf count selected d idx k 0 active innerPre innerSuf row inv cursor innerCursor

theorem NDCallRank2Plain (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (innerCursor : active=innerPre++row::innerSuf) :
    Int.ofNat (Read shards row.2).shard_offsets.length=Int.ofNat (Read shards row.2).shard_sizes.length :=
  NDCallRank2 shards dims order pre suf count selected d idx k 0 active innerPre innerSuf row inv cursor innerCursor

theorem NDInnerIndexSafePlain (shards : List ShardMetadata) (dims order : List Int)
    (count selected d k : Int) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int)
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (innerCursor : active=innerPre++row::innerSuf)
    (bad : ¬(0≤(if row.2<0 then Int.ofNat shards.length+row.2 else row.2) ∧
      (if row.2<0 then Int.ofNat shards.length+row.2 else row.2)<Int.ofNat shards.length)) : False :=
  NDInnerIndexSafe shards dims order count selected d k 0 active innerPre innerSuf row inv innerCursor bad

theorem NDFound (shards : List ShardMetadata) (dims order pre suf : List Int)
    (count selected d idx k : Int) (cut : Nat) (active innerPre innerSuf : List (Int × Int)) (row : Int × Int) (value : Bool)
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
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
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
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
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length)
    (scan : Scanned shards idx (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807))) inner)
    (done : inner=Int.ofNat (active.drop (VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807))).length) :
    _find_nd_overlapping_shards__inv_72 shards dims count selected d order
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
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (cursor : order=pre++idx::suf) (hi : k=Int.ofNat pre.length)
    (scan : Scanned shards idx active inner) (done : inner=Int.ofNat active.length)
    (zero : VeriPy.bisectRight ActiveLex active (Start shards d idx,9223372036854775807)=0) :
    _find_nd_overlapping_shards__inv_72 shards dims count selected d order
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
    (inv : _find_nd_overlapping_shards__inv_72 shards dims count selected d order active k)
    (done : k=Int.ofNat order.length) : _find_nd_overlapping_shards__post shards dims none := by
  have processed:=inv.2.2
  rw [done] at processed
  exact SearchComplete shards dims order d ranks inv.1 processed

-- Checked function proofs; these refer to the unchanged generated models.
@[spec]
theorem _check_shard_metadata_pair_overlap__proof («shard1» : «ShardMetadata») («shard2» : «ShardMetadata») (__vp_h0 : (((Int.ofNat ((«shard1»).«shard_offsets»).length) = (Int.ofNat ((«shard1»).«shard_sizes»).length)) ∧ ((Int.ofNat ((«shard1»).«shard_sizes»).length) = (Int.ofNat ((«shard2»).«shard_offsets»).length)) ∧ ((Int.ofNat ((«shard2»).«shard_offsets»).length) = (Int.ofNat ((«shard2»).«shard_sizes»).length)))) :
  ⦃⌜True⌝⦄ «_check_shard_metadata_pair_overlap» «shard1» «shard2» ⦃(fun __vp_result => ⌜(«_check_shard_metadata_pair_overlap__post» «shard1» «shard2» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_check_shard_metadata_pair_overlap__error» «shard1» «shard2» __vp_error)⌝, ())⦄ := by
  mvcgen [«_check_shard_metadata_pair_overlap», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 23; exact (by (first | veripy_capture «ndims» | veripy_let «ndims» := (Int.ofNat ((«shard1»).«shard_offsets»).length) | veripy_capture_type «ndims» : Int); exact Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜«_check_shard_metadata_pair_overlap__post» «shard1» «shard2» __vp_return⌝) (onContinue := fun __vp_cursor «__vp_index_23» => ⌜(«_check_shard_metadata_pair_overlap__inv_23» «shard1» «shard2» «ndims» «__vp_index_23») ∧ «__vp_index_23» = Int.ofNat __vp_cursor.prefix.length⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)))
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
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «ActiveEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveInsert» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActivePairRanks» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveSuffix» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AllPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAfter» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAuxFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectBefore» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BuildKey» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedMap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CursorRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsAvailable» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsFromIndices» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DomainMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «EarlierDifferent» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortMembers» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortOrdered» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexHead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidOffset» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidSize» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFoundPlain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDMapRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderDomain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderPerm» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderReadNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderStarts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OverlapSymmetric» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairFalse» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairResult» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStepCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ProcessedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeDistinct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeFailure» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeLength» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RanksMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadNonnegative» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnExists» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnFromLoop» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchOverlapWitness» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SelectedDimension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SeparatedExpired» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SweepStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TakeNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «ActiveEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveInsert» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActivePairRanks» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveSuffix» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ActiveTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «AllPairs» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAfter» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectAuxFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectBefore» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BisectFacts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BuildKey» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedMap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CheckedRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «CursorRead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsAvailable» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DimensionsFromIndices» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «DomainMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «EarlierDifferent» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortMembers» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «InsortOrdered» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexHead» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexIntsTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidOffset» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDChooseInvalidSize» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFound» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDFoundPlain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDMapRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NDScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderDomain» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderPerm» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderReadNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OrderStarts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OverlapSymmetric» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairFalse» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairPost» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairResult» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PairStepCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ProcessedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeDistinct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeFailure» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeLength» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RangeMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RanksMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReadNonnegative» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnExists» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ReturnFromLoop» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedEmpty» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ScannedStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchOverlapWitness» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SelectedDimension» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SeparatedExpired» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SweepStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «TakeNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«_check_shard_metadata_pair_overlap__post», «_check_shard_metadata_pair_overlap__error»] | grind [«NDFound», «NDFoundPlain», «NDScannedStep», «PairFalse», «PairInit», «PairPost», «PairResult», «PairStep», «PairStepCursor», «_check_shard_metadata_pair_overlap__inv_23», «_check_shard_metadata_pair_overlap__post», «_check_shard_metadata_pair_overlap__error»] | grind (lax := true) [«ActiveEmpty», «ActiveInsert», «ActivePairRanks», «ActiveSuffix», «ActiveTotal», «ActiveTrans», «AllPairs», «BisectAfter», «BisectAuxFacts», «BisectBefore», «BisectFacts», «BuildKey», «CheckedMap», «CheckedRead», «CursorRead», «DimensionCursor», «DimensionsAvailable», «DimensionsFromIndices», «DomainMember», «EarlierDifferent», «InsortMembers», «InsortOrdered», «LexHead», «LexIntsTotal», «LexIntsTrans», «NDChooseInvalidOffset», «NDChooseInvalidSize», «NDFound», «NDFoundPlain», «NDMapRows», «NDScannedStep», «OrderCursor», «OrderDomain», «OrderPerm», «OrderReadNext», «OrderStarts», «OverlapSymmetric», «PairFalse», «PairInit», «PairPost», «PairResult», «PairStep», «PairStepCursor», «ProcessedEmpty», «RangeCursor», «RangeDistinct», «RangeFailure», «RangeLength», «RangeMember», «RanksMember», «ReadMember», «ReadNonnegative», «ReturnExists», «ReturnFromLoop», «ScannedEmpty», «ScannedStep», «SearchOverlapWitness», «SelectedDimension», «SeparatedExpired», «SweepStep», «TakeNext», «_check_shard_metadata_pair_overlap__inv_23», «_check_shard_metadata_pair_overlap__post», «_check_shard_metadata_pair_overlap__error»]
  )

theorem NDZero (n : Nat) (h : ¬ (n : Int) ≠ 0) : n=0 := by omega
@[spec]
theorem _find_nd_overlapping_shards__proof («shards» : (List «ShardMetadata»)) («sharded_dims» : (List Int)) (__vp_h0 : (((Int.ofNat («shards»).length) ≤ (9223372036854775807 : Int)))) (__vp_h1 : ((((Int.ofNat («shards»).length) ≤ (1 : Int))) ∨ (((Int.ofNat («sharded_dims»).length) > (0 : Int))))) (__vp_h2 : (∀ «a» : Int, (0 ≤ «a» ∧ «a» < (Int.ofNat («shards»).length)) → ((((Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_offsets»).length) = (Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_sizes»).length))) ∧ (((Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_offsets»).length) = (Int.ofNat ((((«shards»).getD ((0 : Int)).toNat default)).«shard_offsets»).length)))))) (__vp_h3 : (∀ «a» : Int, (0 ≤ «a» ∧ «a» < (Int.ofNat («shards»).length)) → (∀ «k» : Int, (0 ≤ «k» ∧ «k» < (Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_sizes»).length)) → (((((((«shards»).getD («a»).toNat default)).«shard_sizes»).getD («k»).toNat default) > (0 : Int)))))) (__vp_h4 : ((((Int.ofNat («shards»).length) = (0 : Int))) ∨ (∀ «k» : Int, (0 ≤ «k» ∧ «k» < (Int.ofNat («sharded_dims»).length)) → (((0 : Int) ≤ ((«sharded_dims»).getD («k»).toNat default)) ∧ (((«sharded_dims»).getD («k»).toNat default) < (Int.ofNat ((((«shards»).getD ((0 : Int)).toNat default)).«shard_offsets»).length)))))) :
  ⦃⌜True⌝⦄ «_find_nd_overlapping_shards» «shards» «sharded_dims» ⦃(fun __vp_result => ⌜(«_find_nd_overlapping_shards__post» «shards» «sharded_dims» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_find_nd_overlapping_shards__error» «shards» «sharded_dims» __vp_error)⌝, ())⦄ := by
  mvcgen [«_find_nd_overlapping_shards», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 54; exact (by (first | veripy_capture «dims» | veripy_let «dims» := (Int.ofNat («sharded_dims»).length) | veripy_capture_type «dims» : Int); exact ⇓⟨__vp_cursor, «sweep_dim_idx», «max_size», «__vp_index_54»⟩ => ⌜(«_find_nd_overlapping_shards__inv_54» «shards» «sharded_dims» «dims» «sweep_dim_idx» «max_size» «__vp_index_54») ∧ «__vp_index_54» = Int.ofNat __vp_cursor.prefix.length⌝))
  all_goals try (veripy_loop_tag 72; exact (by (first | veripy_capture «dims» | veripy_let «dims» := (Int.ofNat («sharded_dims»).length) | veripy_capture_type «dims» : Int); (first | veripy_capture «sweep_dim_idx» | veripy_let «sweep_dim_idx» := (0 : Int) | veripy_capture_type «sweep_dim_idx» : Int); (first | veripy_capture «sweep_dim» | veripy_let «sweep_dim» := ((«sharded_dims»).getD ((if «sweep_dim_idx» < 0 then Int.ofNat («sharded_dims»).length + «sweep_dim_idx» else «sweep_dim_idx»)).toNat default) | veripy_capture_type «sweep_dim» : Int); (first | veripy_capture «sorted_indices» | veripy_let «sorted_indices» := ((((VeriPy.range 0 (Int.ofNat («shards»).length))).map (fun «idx» => (([(((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «sweep_dim» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «sweep_dim» else «sweep_dim»)).toNat default)] ++ (((«sharded_dims»).filter (fun «d» => decide (((«d» ≠ «sweep_dim»))))).map (fun «d» => (((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «d» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «d» else «d»)).toNat default)))), «idx»))).mergeSort (fun a b => VeriPy.lexInts a.1 b.1)).map Prod.snd | veripy_capture_type «sorted_indices» : (List Int)); exact Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜«_find_nd_overlapping_shards__post» «shards» «sharded_dims» __vp_return⌝) (onContinue := fun __vp_cursor («active», «__vp_index_72») => ⌜(«_find_nd_overlapping_shards__inv_72» «shards» «sharded_dims» «dims» «sweep_dim_idx» «sweep_dim» «sorted_indices» «active» «__vp_index_72») ∧ «__vp_index_72» = Int.ofNat __vp_cursor.prefix.length⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)))
  all_goals try (veripy_loop_tag 85; exact (by (first | veripy_capture «dims» | veripy_let «dims» := (Int.ofNat («sharded_dims»).length) | veripy_capture_type «dims» : Int); (first | veripy_capture «sweep_dim_idx» | veripy_let «sweep_dim_idx» := (0 : Int) | veripy_capture_type «sweep_dim_idx» : Int); (first | veripy_capture «sweep_dim» | veripy_let «sweep_dim» := ((«sharded_dims»).getD ((if «sweep_dim_idx» < 0 then Int.ofNat («sharded_dims»).length + «sweep_dim_idx» else «sweep_dim_idx»)).toNat default) | veripy_capture_type «sweep_dim» : Int); (first | veripy_capture «sorted_indices» | veripy_let «sorted_indices» := ((((VeriPy.range 0 (Int.ofNat («shards»).length))).map (fun «idx» => (([(((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «sweep_dim» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «sweep_dim» else «sweep_dim»)).toNat default)] ++ (((«sharded_dims»).filter (fun «d» => decide (((«d» ≠ «sweep_dim»))))).map (fun «d» => (((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).getD ((if «d» < 0 then Int.ofNat ((((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default)).«shard_offsets»).length + «d» else «d»)).toNat default)))), «idx»))).mergeSort (fun a b => VeriPy.lexInts a.1 b.1)).map Prod.snd | veripy_capture_type «sorted_indices» : (List Int)); (first | veripy_capture «active» | veripy_let «active» := [] | veripy_capture_type «active» : (List (Int × Int))); (first | veripy_capture «__vp_index_72» | veripy_capture_type «__vp_index_72» : Int); (first | veripy_capture «idx» | veripy_cursor «idx» 72 0 0 0 | veripy_capture_type «idx» : Int); (first | veripy_capture «current» | veripy_let «current» := ((«shards»).getD ((if «idx» < 0 then Int.ofNat («shards»).length + «idx» else «idx»)).toNat default) | veripy_capture_type «current» : «ShardMetadata»); (first | veripy_capture «start» | veripy_let «start» := (((«current»).«shard_offsets»).getD ((if «sweep_dim» < 0 then Int.ofNat ((«current»).«shard_offsets»).length + «sweep_dim» else «sweep_dim»)).toNat default) | veripy_capture_type «start» : Int); (first | veripy_capture «end» | veripy_let «end» := («start» + (((«current»).«shard_sizes»).getD ((if «sweep_dim» < 0 then Int.ofNat ((«current»).«shard_sizes»).length + «sweep_dim» else «sweep_dim»)).toNat default)) | veripy_capture_type «end» : Int); (first | veripy_capture «cutoff» | veripy_let «cutoff» := (Int.ofNat (VeriPy.bisectRight (fun a b => decide ((a).1 < (b).1 ∨ ((a).1 = (b).1 ∧ ((a).2 ≤ (b).2)))) «active» («start», (9223372036854775807 : Int)))) | veripy_capture_type «cutoff» : Int); exact Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜«_find_nd_overlapping_shards__post» «shards» «sharded_dims» __vp_return⌝) (onContinue := fun __vp_cursor «__vp_index_85» => ⌜(«_find_nd_overlapping_shards__inv_85» «shards» «sharded_dims» «dims» «sweep_dim_idx» «sweep_dim» «sorted_indices» «active» «__vp_index_72» «idx» «current» «start» «end» «cutoff» «__vp_index_85») ∧ «__vp_index_85» = Int.ofNat __vp_cursor.prefix.length⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)))
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
    _find_1d_overlapping_shards__inv_114 shards dim rows 0 := by
  intro j hj; omega

theorem SearchStep (shards : List ShardMetadata) (dim i : Int) (rows : List Row)
    (inv : _find_1d_overlapping_shards__inv_114 shards dim rows i)
    (hi : 0≤i)
    (pair : (rows.getD i.toNat default).2.1 < (rows.getD (i+1).toNat default).1) :
    _find_1d_overlapping_shards__inv_114 shards dim rows (i+1) := by
  intro j hj
  by_cases he : j=i
  · subst j
    simpa only [if_neg (show ¬i+1<0 by omega)] using pair
  · exact inv j (by omega)

theorem SearchDone (shards : List ShardMetadata) (dim : Int)
    (inv : _find_1d_overlapping_shards__inv_114 shards dim ((Rows shards dim).mergeSort Lex) (Int.ofNat (Int.ofNat shards.length-1).toNat)) :
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

theorem OneDRangeCursor (n cur : Int) (pre suf : List Int)
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
  have h:=OneDRangeCursor _ _ _ _ hc
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
    (inv : _find_1d_overlapping_shards__inv_114 shards dim (rows.mergeSort Lex) i)
    (pair : ¬(rows.mergeSort Lex |>.getD cur.toNat default).2.1 ≥
       (rows.mergeSort Lex |>.getD (if cur+1<0 then Int.ofNat (rows.mergeSort Lex).length+(cur+1) else cur+1).toNat default).1) :
    _find_1d_overlapping_shards__inv_114 shards dim (rows.mergeSort Lex) (i+1) := by
  have h:=OneDRangeCursor _ _ _ _ hc
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
  have h:=OneDRangeCursor _ _ _ _ hc
  have h0 : cur.toNat<((Rows shards dim).mergeSort Lex).length := by simp only [List.length_mergeSort,RowLength]; change cur.toNat<shards.length; have := h.2; simp only [VeriPy.ofNat_cast] at this; omega
  have h1 : cur.toNat+1<((Rows shards dim).mergeSort Lex).length := by simp only [List.length_mergeSort,RowLength]; have := h.2; simp only [VeriPy.ofNat_cast] at this; omega
  have hn : ¬cur+1<0 := by omega
  have he : (cur+1).toNat=cur.toNat+1 := by omega
  simp only [if_neg hn,he,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1,Option.getD_some] at pair ⊢
  exact ⟨_,rfl,FoundOverlap shards dim cur.toNat domain h1 pair⟩

theorem SearchReturn (shards : List ShardMetadata) (dim : Int) (rows : List Row)
    (r : Option (Option (Int × Int)) × Int) (a : Option (Int × Int))
    (h : r.1=none ∧ _find_1d_overlapping_shards__inv_114 shards dim (rows.mergeSort Lex) r.2 ∧ r.2=Int.ofNat (VeriPy.range 0 (Int.ofNat shards.length-1)).length ∨
      ∃ a, r.1=some a ∧ _find_1d_overlapping_shards__post shards dim a)
    (returned : r.1=some a) : _find_1d_overlapping_shards__post shards dim a := by
  rcases h with h | ⟨b,hb,post⟩
  · rw [returned] at h; simp at h
  · have he : a=b := Option.some.inj (returned.symm.trans hb); simpa only [he] using post

theorem SearchFinish (shards : List ShardMetadata) (dim : Int) (rows : List Row)
    (r : Option (Option (Int × Int)) × Int) (hr : rows=Rows shards dim)
    (h : r.1=none ∧ _find_1d_overlapping_shards__inv_114 shards dim (rows.mergeSort Lex) r.2 ∧ r.2=Int.ofNat (VeriPy.range 0 (Int.ofNat shards.length-1)).length ∨
      ∃ a, r.1=some a ∧ _find_1d_overlapping_shards__post shards dim a)
    (returned : r.1=none) : _find_1d_overlapping_shards__post shards dim none := by
  rcases h with ⟨_,inv,hi⟩ | ⟨a,ha,_⟩
  · subst rows
    rw [hi] at inv
    apply SearchDone
    simpa only [VeriPy.range,Int.sub_zero,List.length_map,List.length_range] using inv
  · rw [returned] at ha; contradiction

@[spec]
theorem _find_1d_overlapping_shards__proof («shards» : (List «ShardMetadata»)) («dim» : Int) (__vp_h0 : (∀ «j» : Int, (0 ≤ «j» ∧ «j» < (Int.ofNat («shards»).length)) → ((((0 : Int) ≤ «dim») ∧ («dim» < (Int.ofNat ((((«shards»).getD («j»).toNat default)).«shard_offsets»).length))) ∧ (((Int.ofNat ((((«shards»).getD («j»).toNat default)).«shard_sizes»).length) = (Int.ofNat ((((«shards»).getD («j»).toNat default)).«shard_offsets»).length))) ∧ (((((((«shards»).getD («j»).toNat default)).«shard_sizes»).getD ((if «dim» < 0 then Int.ofNat ((((«shards»).getD («j»).toNat default)).«shard_sizes»).length + «dim» else «dim»)).toNat default) > (0 : Int)))))) :
  ⦃⌜True⌝⦄ «_find_1d_overlapping_shards» «shards» «dim» ⦃(fun __vp_result => ⌜(«_find_1d_overlapping_shards__post» «shards» «dim» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«_find_1d_overlapping_shards__error» «shards» «dim» __vp_error)⌝, ())⦄ := by
  mvcgen [«_find_1d_overlapping_shards», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (exact (by (first | veripy_capture «intervals» | let «intervals» := (((((«shards»).zipIdx.map (fun (x,i) => (Int.ofNat i,x)))).map (fun («i», «s») => ((((«s»).«shard_offsets»).getD ((if «dim» < 0 then Int.ofNat ((«s»).«shard_offsets»).length + «dim» else «dim»)).toNat default), (((((«s»).«shard_offsets»).getD ((if «dim» < 0 then Int.ofNat ((«s»).«shard_offsets»).length + «dim» else «dim»)).toNat default) + (((«s»).«shard_sizes»).getD ((if «dim» < 0 then Int.ofNat ((«s»).«shard_sizes»).length + «dim» else «dim»)).toNat default)) - (1 : Int)), «i»)))).mergeSort (fun a b => decide ((a).1 < (b).1 ∨ ((a).1 = (b).1 ∧ ((a).2.1 < (b).2.1 ∨ ((a).2.1 = (b).2.1 ∧ ((a).2.2 ≤ (b).2.2))))))); exact Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜«_find_1d_overlapping_shards__post» «shards» «dim» __vp_return⌝) (onContinue := fun __vp_cursor «__vp_index_114» => ⌜(«_find_1d_overlapping_shards__inv_114» «shards» «dim» «intervals» «__vp_index_114») ∧ «__vp_index_114» = Int.ofNat __vp_cursor.prefix.length⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)))
  all_goals (
    try (simp only [decide_eq_true_eq, WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals try veripy_project_facts
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals try veripy_fold_projections
    all_goals try (simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at *)
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega | (solve | apply «BuildRow» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BuildRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FoundOverlap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NoAdjacentOverlap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PermutedDisjoint» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PermutedRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OneDRangeCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowIds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowIdsDistinct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowIncluded» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowLength» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowsMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchDone» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchFinish» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchFoundCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchInvalidFirst» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchInvalidNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchReturn» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchSafety» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchStepCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ShardDisjoint» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedRowFact» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedStarts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (exfalso; first | (solve | apply «BuildRow» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «BuildRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «FoundOverlap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexTotal» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «LexTrans» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «NoAdjacentOverlap» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PermutedDisjoint» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «PermutedRows» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «OneDRangeCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowAt» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowIds» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowIdsDistinct» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowIncluded» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowLength» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «RowsMember» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchDone» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchFinish» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchFoundCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchInit» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchInvalidFirst» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchInvalidNext» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchReturn» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchSafety» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchStep» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SearchStepCursor» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «ShardDisjoint» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedRowFact» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega) | (solve | apply «SortedStarts» <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)) | grind [«_find_1d_overlapping_shards__post», «_find_1d_overlapping_shards__error»] | grind [«BuildRow», «BuildRows», «FoundOverlap», «LexTotal», «LexTrans», «NoAdjacentOverlap», «PermutedDisjoint», «PermutedRows», «OneDRangeCursor», «RowAt», «RowIds», «RowIdsDistinct», «RowIncluded», «RowLength», «RowsMember», «SearchDone», «SearchFinish», «SearchFoundCursor», «SearchInit», «SearchInvalidFirst», «SearchInvalidNext», «SearchReturn», «SearchSafety», «SearchStep», «SearchStepCursor», «ShardDisjoint», «SortedRowFact», «SortedStarts», «_find_1d_overlapping_shards__inv_114», «_find_1d_overlapping_shards__post», «_find_1d_overlapping_shards__error»]
  )
theorem PositiveVolume (sizes : List Int) (positive : ∀ s∈sizes, s>0) : sizes.prod>0 := by
  induction sizes with
  | nil => decide
  | cons x xs ih =>
    simp only [List.prod_cons]
    exact Int.mul_pos (positive x (by simp)) (ih (fun y hy => positive y (by simp [hy])))

theorem PartitionEmpty (shards : List ShardMetadata) : Partitioned shards [] 0 := by
  constructor
  · intro k hk;simp only [List.length_nil,VeriPy.ofNat_cast] at hk;omega
  · intro d hd;omega

theorem PartitionAdvanceAdd (shards : List ShardMetadata) (dims : List Int) (d : Int)
    (partition : Partitioned shards dims d) (nonnegative : 0≤d) : Partitioned shards (dims++[d]) (d+1) := by
  constructor
  · intro k hk
    have hm := ReadMember (dims++[d]) k hk
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨n,hn,he⟩:=List.mem_iff_getElem.mp hm
      have hd:=partition.1 (Int.ofNat n) (by simp only [VeriPy.ofNat_cast];omega)
      have read : Read dims (Int.ofNat n)=dims[n] := by simp [Read,VeriPy.ofNat_cast,Int.not_ofNat_neg,List.getD_eq_getElem?_getD,hn]
      rw [read,he] at hd
      exact ⟨hd.1,by omega⟩
    · have eq:=List.mem_singleton.mp hm
      rw [eq];omega
  · intro q hq absent a ha
    have old : q∉dims := fun h => absent (List.mem_append_left _ h)
    have neq : q≠d := by intro he;subst q;apply absent;simp
    exact partition.2 q (by omega) old a ha

theorem PartitionAdvanceSame (shards : List ShardMetadata) (dims : List Int) (d : Int)
    (partition : Partitioned shards dims d) (same : SamePrefix shards d (Int.ofNat shards.length)) :
    Partitioned shards dims (d+1) := by
  constructor
  · intro k hk;have hd:=partition.1 k hk;exact ⟨hd.1,by omega⟩
  · intro q hq absent a ha
    by_cases equal : q=d
    · subst q;exact same a ha
    · exact partition.2 q (by omega) absent a ha

theorem SamePrefixInit (shards : List ShardMetadata) (d : Int) : SamePrefix shards d 1 := by
  intro a ha
  have equal : a=0 := by omega
  subst a;exact ⟨rfl,rfl⟩

theorem SamePrefixStep (shards : List ShardMetadata) (d k : Int) (same : SamePrefix shards d k)
    (offset : Read (Read shards k).shard_offsets d=Read (Read shards 0).shard_offsets d)
    (size : Read (Read shards k).shard_sizes d=Read (Read shards 0).shard_sizes d) : SamePrefix shards d (k+1) := by
  intro a ha
  by_cases equal : a=k
  · subst a;exact ⟨offset,size⟩
  · exact same a (by omega)

theorem PartitionAdvance (shards : List ShardMetadata) (dims : List Int) (d : Int)
    (partition : Partitioned shards dims d) (nonnegative : 0≤d) :
    Partitioned shards (dims++[d]) (d+1) ∧ (SamePrefix shards d (Int.ofNat shards.length) → Partitioned shards dims (d+1)) :=
  ⟨PartitionAdvanceAdd shards dims d partition nonnegative,PartitionAdvanceSame shards dims d partition⟩

theorem RangeFromCursor (lo hi cur : Int) (pre suf : List Int)
    (cursor : VeriPy.range lo hi=pre++cur::suf) :
    cur=lo+Int.ofNat pre.length ∧ lo≤cur ∧ cur<hi := by
  have length : pre.length<(hi-lo).toNat := by
    have h:=congrArg List.length cursor
    simp only [VeriPy.range,List.length_map,List.length_range,List.length_append,List.length_cons] at h
    omega
  have read : (VeriPy.range lo hi).getD pre.length 0=cur := by
    rw [cursor];simp [List.getD_eq_getElem?_getD]
  have value : (VeriPy.range lo hi).getD pre.length 0=lo+Int.ofNat pre.length := by
    simp [VeriPy.range,List.getD_eq_getElem?_getD,length]
  rw [value] at read
  refine ⟨read.symm,?_,?_⟩ <;> rw [←read]
  · have h:=Int.natCast_nonneg pre.length;simp only [VeriPy.ofNat_cast] at *;omega
  · have h:=Int.lt_of_toNat_lt (show (Int.ofNat pre.length).toNat<(hi-lo).toNat from length)
    simp only [VeriPy.ofNat_cast] at *;omega

theorem ValidationTrivial (shards : List ShardMetadata) (small : Int.ofNat shards.length≤1) :
    validate_non_overlapping_shards_metadata__post shards () := by
  simp only [validate_non_overlapping_shards_metadata__post,false_iff]
  rintro ⟨a,ha,b,hb,overlap⟩
  omega

theorem ValidationDimension (shards : List ShardMetadata) (i d : Int) (ranks : Ranks shards)
    (index : 0≤i ∧ i<Int.ofNat shards.length)
    (dimension : 0≤d ∧ d<Int.ofNat (Read shards 0).shard_offsets.length) :
    (0≤d ∧ d<Int.ofNat (Read shards i).shard_offsets.length) ∧
    (0≤d ∧ d<Int.ofNat (Read shards i).shard_sizes.length) := by
  have rank:=ranks i index
  have read : Read shards i=shards.getD i.toNat default := ReadNonnegative shards i index.1
  have zero : Read shards 0=shards.getD 0 default := by rfl
  simp only [read,zero] at *
  have r:=rank.1
  have r0:=rank.2
  constructor <;> constructor <;> omega

theorem ValidationDimensionRaw (shards : List ShardMetadata) (i d : Int) (ranks : Ranks shards)
    (index : 0≤i ∧ i<Int.ofNat shards.length)
    (dimension : 0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length) :
    (0≤d ∧ d<Int.ofNat (shards.getD i.toNat default).shard_offsets.length) ∧
    (0≤d ∧ d<Int.ofNat (shards.getD i.toNat default).shard_sizes.length) := by
  have shape:=ValidationDimension shards i d ranks index dimension
  simpa only [Read,if_neg (show ¬i<0 by omega)] using shape

theorem ValidationFirstFailure (shards : List ShardMetadata) (nonempty : shards≠[])
    (bad : ¬0<Int.ofNat shards.length) : False := by
  have length:=List.length_pos_iff.mpr nonempty
  simp only [VeriPy.ofNat_cast] at bad;omega

theorem ValidationAllRows (shards : List ShardMetadata) (nonempty : 0<Int.ofNat shards.length) :
    ∀ x∈shards,
      (do let first ← VeriPy.get shards 0
          if x.shard_offsets=List.replicate first.shard_offsets.length 0 then
            pure (decide (x.shard_sizes.prod=0)) else pure false : Except VeriPy.Error Bool) =
      Except.ok (decide (x.shard_offsets=List.replicate (shards.getD 0 default).shard_offsets.length 0 ∧ x.shard_sizes.prod=0)) := by
  intro x hx
  have length : 0<shards.length := by simp only [VeriPy.ofNat_cast] at nonempty;omega
  simp [VeriPy.get,length]
  split <;> simp_all
  all_goals rfl

theorem ValidationNDNone (shards : List ShardMetadata) (dims : List Int)
    (post : _find_nd_overlapping_shards__post shards dims none) :
    validate_non_overlapping_shards_metadata__post shards () := by
  have no:=post.2.2
  simp only [not_true_eq_false,false_or] at no
  constructor
  · intro h;contradiction
  · rintro ⟨a,ha,b,hb,overlap⟩
    apply no
    refine ⟨a,ha,b,⟨by omega,hb.2⟩,by omega,?_⟩
    simpa only [if_neg (show ¬b<0 by omega)] using overlap

theorem ValidationOrderedWitness (shards : List ShardMetadata) (a b : Int)
    (ha : 0≤a ∧ a<Int.ofNat shards.length) (hb : a+1≤b ∧ b<Int.ofNat shards.length)
    (overlap : ShardsOverlap (Read shards a) (Read shards b)) :
    validate_non_overlapping_shards_metadata__error shards VeriPy.Error.value := by
  refine ⟨rfl,?_⟩
  constructor
  · intro _
    refine ⟨a,ha,b,hb,?_⟩
    have na : ¬a<0 := by omega
    have nb : ¬b<0 := by omega
    intro d hd
    have h:=overlap.2.2.2 d (by simpa only [Read,if_neg na] using hd)
    simpa only [Read,if_neg na,if_neg nb,if_neg (show ¬d<0 by omega)] using h
  · intro _;trivial

theorem ValidationWitness (shards : List ShardMetadata) (a b : Int)
    (ha : 0≤a ∧ a<Int.ofNat shards.length) (hb : 0≤b ∧ b<Int.ofNat shards.length)
    (distinct : a≠b) (overlap : ShardsOverlap (Read shards a) (Read shards b)) :
    validate_non_overlapping_shards_metadata__error shards VeriPy.Error.value := by
  by_cases ordered : a<b
  · exact ValidationOrderedWitness shards a b ha ⟨by omega,hb.2⟩ overlap
  · exact ValidationOrderedWitness shards b a hb ⟨by omega,ha.2⟩ ((OverlapSymmetric _ _).mp overlap)

theorem PartitionScanStep (shards : List ShardMetadata) (dims pre suf : List Int) (d k i : Int)
    (nontrivial : 1<Int.ofNat shards.length)
    (cursor : VeriPy.range 1 (Int.ofNat shards.length)=pre++i::suf)
    (index : k=Int.ofNat pre.length)
    (partition : Partitioned shards dims d) (same : SamePrefix shards d (1+k))
    (offset : Read (Read shards i).shard_offsets d=Read (Read shards 0).shard_offsets d)
    (size : Read (Read shards i).shard_sizes d=Read (Read shards 0).shard_sizes d) :
    if suf=[] then Partitioned shards dims (d+1)
    else Partitioned shards dims d ∧ SamePrefix shards d (1+(k+1)) ∧ k+1=Int.ofNat pre.length+1 := by
  have bounds:=RangeFromCursor 1 (Int.ofNat shards.length) i pre suf cursor
  have equal : i=1+k := by rw [index];exact bounds.1
  have next:=SamePrefixStep shards d i (by simpa only [equal] using same) offset size
  by_cases finished : suf=[]
  · simp only [finished,if_true]
    have length:=congrArg List.length cursor
    simp only [VeriPy.range,List.length_map,List.length_range,List.length_append,List.length_cons,finished,List.length_nil] at length
    have last : i+1=Int.ofNat shards.length := by
      simp only [VeriPy.ofNat_cast] at *;omega
    apply PartitionAdvanceSame shards dims d partition
    simpa only [last] using next
  · simp only [finished,if_false]
    refine ⟨partition,?_,?_⟩
    · have eq : 1+(k+1)=i+1 := by omega
      rw [eq];exact next
    · simp only [List.length_append,List.length_cons,List.length_nil,VeriPy.ofNat_cast,Int.natCast_add,Int.natCast_one,Int.natCast_zero] at *;omega

theorem PartitionScanInit (shards : List ShardMetadata) (dims : List Int) (d : Int)
    (nontrivial : 1<Int.ofNat shards.length) (partition : Partitioned shards dims d) :
    if VeriPy.range 1 (Int.ofNat shards.length)=[] then Partitioned shards dims (d+1)
    else Partitioned shards dims d ∧ SamePrefix shards d (1+0) ∧ True := by
  have nonempty : VeriPy.range 1 (Int.ofNat shards.length)≠[] := by
    intro empty
    have length:=congrArg List.length empty
    simp only [VeriPy.range,List.length_map,List.length_range,List.length_nil,VeriPy.ofNat_cast] at *;omega
  simp only [nonempty,if_false]
  exact ⟨partition,SamePrefixInit shards d,trivial⟩

theorem PartitionOuterStep (shards : List ShardMetadata) (dims pre suf : List Int) (d k : Int)
    (cursor : VeriPy.range 0 (Int.ofNat (shards.getD 0 default).shard_offsets.length)=pre++d::suf)
    (index : k=Int.ofNat pre.length) (partition : Partitioned shards dims (d+1)) :
    validate_non_overlapping_shards_metadata__inv_141 shards dims (k+1) := by
  have equal:=(RangeCursor _ d pre suf cursor).1
  have eq : d=k := equal.trans index.symm
  simpa only [validate_non_overlapping_shards_metadata__inv_141,Int.zero_add,eq] using partition

theorem ValidationNDReturn (shards : List ShardMetadata) (dims : List Int) (value : Option (Int × Int))
    (post : _find_nd_overlapping_shards__post shards dims value) (none : ¬value≠Option.none) :
    validate_non_overlapping_shards_metadata__post shards () := by
  have equal : value=Option.none := Classical.not_not.mp none
  subst value
  exact ValidationNDNone shards dims post

theorem PartitionScanInitFromOuter (shards : List ShardMetadata) (dims pre suf : List Int) (d k : Int)
    (nontrivial : 1<Int.ofNat shards.length)
    (cursor : VeriPy.range 0 (Int.ofNat (shards.getD 0 default).shard_offsets.length)=pre++d::suf)
    (index : k=Int.ofNat pre.length)
    (inv : validate_non_overlapping_shards_metadata__inv_141 shards dims k) :
    if VeriPy.range 1 (Int.ofNat shards.length)=[] then Partitioned shards dims (d+1)
    else Partitioned shards dims d ∧ SamePrefix shards d (1+0) ∧ True := by
  apply PartitionScanInit shards dims d nontrivial
  have eq : d=k := (RangeCursor _ d pre suf cursor).1.trans index.symm
  simpa only [validate_non_overlapping_shards_metadata__inv_141,Int.zero_add,eq] using inv

theorem ValidationAllRowsRaw (shards : List ShardMetadata) (nonempty : 0<(shards.length:Int)) :
    ∀ x∈shards,
      (do let first ← if 0<(shards.length:Int) then pure (shards.getD 0 default) else VeriPy.raise VeriPy.Error.index
          if x.shard_offsets=List.replicate first.shard_offsets.length 0 then
            pure (decide (x.shard_sizes.prod=0)) else pure false : Except VeriPy.Error Bool) =
      Except.ok (decide (x.shard_offsets=List.replicate (shards.getD 0 default).shard_offsets.length 0 ∧ x.shard_sizes.prod=0)) := by
  intro x hx
  simp only [if_pos nonempty]
  simp
  split <;> simp_all
  all_goals rfl

theorem ValidationPositiveMember (shards : List ShardMetadata) (s : ShardMetadata)
    (positive : ∀ a : Int, (0≤a ∧ a<Int.ofNat shards.length) → ∀ k : Int,
      (0≤k ∧ k<Int.ofNat (shards.getD a.toNat default).shard_sizes.length) →
        (shards.getD a.toNat default).shard_sizes.getD k.toNat default>0)
    (member : s∈shards) : ∀ x∈s.shard_sizes, x>0 := by
  obtain ⟨a,ha,he⟩:=List.mem_iff_getElem.mp member
  have read : shards.getD (Int.ofNat a).toNat default=s := by
    simp only [VeriPy.ofNat_cast,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha,Option.getD_some,he]
  have hp:=positive (Int.ofNat a) (by simp only [VeriPy.ofNat_cast];omega)
  rw [read] at hp
  intro x hx
  obtain ⟨k,hk,hke⟩:=List.mem_iff_getElem.mp hx
  have h:=hp (Int.ofNat k) (by simp only [VeriPy.ofNat_cast];omega)
  simpa only [VeriPy.ofNat_cast,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some,hke] using h

theorem ValidationAllZerosImpossible (shards : List ShardMetadata)
    (positive : ∀ a : Int, (0≤a ∧ a<Int.ofNat shards.length) → ∀ k : Int,
      (0≤k ∧ k<Int.ofNat (shards.getD a.toNat default).shard_sizes.length) →
        (shards.getD a.toNat default).shard_sizes.getD k.toNat default>0)
    (nonempty : 0<Int.ofNat shards.length)
    (all : shards.all (fun x=>decide (x.shard_offsets=List.replicate (shards.getD 0 default).shard_offsets.length 0 ∧ x.shard_sizes.prod=0))=true) : False := by
  have bound : 0<shards.length := by simp only [VeriPy.ofNat_cast] at nonempty;omega
  have member:=List.getElem_mem (l:=shards) (n:=0) bound
  have zero:=(List.all_eq_true.mp all) _ member
  simp only [decide_eq_true_eq] at zero
  have positive:=PositiveVolume _ (ValidationPositiveMember shards _ positive member)
  have :=zero.2
  omega

theorem PartitionOverlap (shards : List ShardMetadata) (dims : List Int) (a b : Int)
    (ranks : Ranks shards)
    (positive : ∀ j : Int, (0≤j ∧ j<Int.ofNat shards.length) → ∀ k : Int,
      (0≤k ∧ k<Int.ofNat (shards.getD j.toNat default).shard_sizes.length) →
        (shards.getD j.toNat default).shard_sizes.getD k.toNat default>0)
    (partition : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (ha : 0≤a ∧ a<Int.ofNat shards.length) (hb : 0≤b ∧ b<Int.ofNat shards.length)
    (selected : ∀ d∈dims,
      Read (Read shards a).shard_offsets d<Read (Read shards b).shard_offsets d+Read (Read shards b).shard_sizes d ∧
      Read (Read shards b).shard_offsets d<Read (Read shards a).shard_offsets d+Read (Read shards a).shard_sizes d) :
    ShardsOverlap (Read shards a) (Read shards b) := by
  have ma:=ReadMember shards a ha
  have mb:=ReadMember shards b hb
  have ra:=RanksMember shards _ ranks ma
  have rb:=RanksMember shards _ ranks mb
  refine ⟨ra.1,rb.1,ra.2.trans rb.2.symm,?_⟩
  intro d hd
  by_cases member : d∈dims
  · exact selected d member
  · have domain : 0≤d ∧ d<Int.ofNat (Read shards 0).shard_offsets.length := by
      change 0≤d ∧ d<Int.ofNat (shards.getD 0 default).shard_offsets.length
      rw [←ra.2];exact hd
    have sa:=partition.2 d domain member a ha
    have sb:=partition.2 d domain member b hb
    have pa:=ValidationPositiveMember shards _ positive ma _
      (ReadMember (Read shards a).shard_sizes d ⟨hd.1,by rw [←ra.1];exact hd.2⟩)
    have pb:=ValidationPositiveMember shards _ positive mb _
      (ReadMember (Read shards b).shard_sizes d ⟨hd.1,by rw [←rb.1,rb.2,←ra.2];exact hd.2⟩)
    constructor <;> omega


theorem PartitionFinal (shards : List ShardMetadata) (dims : List Int) (k : Int)
    (inv : validate_non_overlapping_shards_metadata__inv_141 shards dims k)
    (count : k=Int.ofNat (VeriPy.range 0 (Int.ofNat (shards.getD 0 default).shard_offsets.length)).length) :
    Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length) := by
  have equal : k=Int.ofNat (shards.getD 0 default).shard_offsets.length := by
    simpa only [VeriPy.range,Int.sub_zero,List.length_map,List.length_range,VeriPy.ofNat_cast,Int.toNat_natCast] using count
  change Partitioned shards dims (Int.ofNat (shards.getD 0 default).shard_offsets.length)
  simpa only [validate_non_overlapping_shards_metadata__inv_141,Int.zero_add,equal] using inv

theorem PartitionDimensions (shards : List ShardMetadata) (dims : List Int)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length)) :
    ∀ k : Int, 0≤k → k<Int.ofNat dims.length →
      0≤dims.getD k.toNat default ∧ dims.getD k.toNat default<Int.ofNat (shards.getD 0 default).shard_offsets.length := by
  intro k hk hb
  have h:=part.1 k ⟨hk,hb⟩
  change 0≤Read dims k ∧ Read dims k<Int.ofNat (shards.getD 0 default).shard_offsets.length at h
  simpa only [Read,if_neg (show ¬k<0 by omega)] using h

theorem ValidationNDWitness (shards : List ShardMetadata) (dims : List Int) (value : Option (Int × Int)) (p : Int × Int)
    (ranks : Ranks shards) (post : _find_nd_overlapping_shards__post shards dims value) (some : value=Option.some p) :
    validate_non_overlapping_shards_metadata__error shards VeriPy.Error.value := by
  subst value
  have bounds:=post.1.resolve_left (by simp)
  simp only [Option.getD_some] at bounds
  have overlap:=post.2.1.resolve_left (by simp)
  apply ValidationWitness shards p.1 p.2 bounds.1 bounds.2.1 bounds.2.2
  apply SearchOverlapWitness shards p.1 p.2 ranks bounds.1 bounds.2.1
  simp only [Option.getD_some,if_neg (show ¬p.1<0 by omega),if_neg (show ¬p.2<0 by omega)] at overlap
  intro d hd
  have h : ¬(_ ∨ _) := fun bad => overlap ⟨d,hd,bad⟩
  omega

theorem ValidationPairAccess (shards : List ShardMetadata) (value : Option (Int × Int)) (p : Int × Int)
    (bounds : ¬value≠none ∨ (0≤(value.getD default).1 ∧ (value.getD default).1<Int.ofNat shards.length) ∧
      (0≤(value.getD default).2 ∧ (value.getD default).2<Int.ofNat shards.length) ∧ (value.getD default).1≠(value.getD default).2)
    (some : value=Option.some p) :
    ((0≤if p.1<0 then Int.ofNat shards.length+p.1 else p.1) ∧ (if p.1<0 then Int.ofNat shards.length+p.1 else p.1)<Int.ofNat shards.length) ∧
    ((0≤if p.2<0 then Int.ofNat shards.length+p.2 else p.2) ∧ (if p.2<0 then Int.ofNat shards.length+p.2 else p.2)<Int.ofNat shards.length) := by
  subst value
  have bounds:=bounds.resolve_left (by simp)
  simp only [Option.getD_some] at bounds
  simp only [if_neg (show ¬p.1<0 by omega),if_neg (show ¬p.2<0 by omega)]
  exact ⟨bounds.1,bounds.2.1⟩


theorem Validation1DPre (shards : List ShardMetadata) (dims : List Int)
    (ranks : Ranks shards)
    (positive : ∀ a : Int, (0≤a ∧ a<Int.ofNat shards.length) → ∀ k : Int,
      (0≤k ∧ k<Int.ofNat (shards.getD a.toNat default).shard_sizes.length) →
        (shards.getD a.toNat default).shard_sizes.getD k.toNat default>0)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (nonempty : 0<Int.ofNat dims.length) :
    ∀ j : Int, 0≤j → j<Int.ofNat shards.length →
      (0≤dims.getD 0 default ∧ dims.getD 0 default<Int.ofNat (shards.getD j.toNat default).shard_offsets.length) ∧
      Int.ofNat (shards.getD j.toNat default).shard_sizes.length=Int.ofNat (shards.getD j.toNat default).shard_offsets.length ∧
      (shards.getD j.toNat default).shard_sizes.getD (if dims.getD 0 default<0 then Int.ofNat (shards.getD j.toNat default).shard_sizes.length+dims.getD 0 default else dims.getD 0 default).toNat default>0 := by
  intro j hj hb
  have dim:=PartitionDimensions shards dims part 0 (by omega) nonempty
  change 0≤dims.getD 0 default ∧ dims.getD 0 default<Int.ofNat (shards.getD 0 default).shard_offsets.length at dim
  have good:=ValidationDimensionRaw shards j (dims.getD 0 default) ranks ⟨hj,hb⟩ dim
  have rank:=ranks j ⟨hj,hb⟩
  refine ⟨good.1,rank.1.symm,?_⟩
  rw [if_neg (show ¬dims.getD 0 default<0 by omega)]
  exact positive j ⟨hj,hb⟩ _ good.2

theorem Validation1DNone (shards : List ShardMetadata) (dims : List Int)
    (ranks : Ranks shards)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (nonempty : 0<Int.ofNat dims.length)
    (post : _find_1d_overlapping_shards__post shards (dims.getD 0 default) none) :
    validate_non_overlapping_shards_metadata__post shards () := by
  have dim:=PartitionDimensions shards dims part 0 (by omega) nonempty
  change 0≤dims.getD 0 default ∧ dims.getD 0 default<Int.ofNat (shards.getD 0 default).shard_offsets.length at dim
  have no:=post.2.2
  simp only [not_true_eq_false,false_or] at no
  constructor
  · intro h;contradiction
  · rintro ⟨a,ha,b,hb,overlap⟩
    have separated:=no a ha b ⟨by omega,hb.2⟩
    have bound:=ValidationDimensionRaw shards a _ ranks ha dim
    have pair:=overlap _ bound.1
    simp only [if_neg (show ¬b<0 by omega)] at pair
    simp only [if_neg (show ¬dims.getD 0 default<0 by omega)] at separated
    omega

theorem Validation1DWitness (shards : List ShardMetadata) (dims : List Int) (value : Option (Int × Int)) (p : Int × Int)
    (ranks : Ranks shards)
    (positive : ∀ a : Int, (0≤a ∧ a<Int.ofNat shards.length) → ∀ k : Int,
      (0≤k ∧ k<Int.ofNat (shards.getD a.toNat default).shard_sizes.length) →
        (shards.getD a.toNat default).shard_sizes.getD k.toNat default>0)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (length : Int.ofNat dims.length=1)
    (post : _find_1d_overlapping_shards__post shards (dims.getD 0 default) value)
    (some : value=Option.some p) :
    validate_non_overlapping_shards_metadata__error shards VeriPy.Error.value := by
  subst value
  have bounds:=post.1.resolve_left (by simp)
  simp only [Option.getD_some] at bounds
  have overlap:=post.2.1.resolve_left (by simp)
  apply ValidationWitness shards p.1 p.2 bounds.1 bounds.2.1 bounds.2.2
  apply PartitionOverlap shards dims p.1 p.2 ranks positive part bounds.1 bounds.2.1
  intro d hd
  have singleton : dims=[dims.getD 0 default] := by
    cases dims with
    | nil => simp only [List.length_nil,VeriPy.ofNat_cast] at length;omega
    | cons x xs =>
      have empty : xs=[] := by simp only [List.length_cons,VeriPy.ofNat_cast] at length;exact List.eq_nil_of_length_eq_zero (by omega)
      subst xs;rfl
  rw [singleton] at hd
  have equal:=List.mem_singleton.mp hd
  subst d
  simpa only [Read,Option.getD_some] using overlap


theorem Validation1DReturn (shards : List ShardMetadata) (dims : List Int) (value : Option (Int × Int))
    (ranks : Ranks shards)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (nonempty : 0<Int.ofNat dims.length)
    (post : _find_1d_overlapping_shards__post shards (dims.getD 0 default) value)
    (none : ¬value≠Option.none) : validate_non_overlapping_shards_metadata__post shards () := by
  have equal : value=Option.none := Classical.not_not.mp none
  subst value
  exact Validation1DNone shards dims ranks part nonempty post

theorem ValidationNoDims (shards : List ShardMetadata) (dims : List Int)
    (ranks : Ranks shards)
    (positive : ∀ a : Int, (0≤a ∧ a<Int.ofNat shards.length) → ∀ k : Int,
      (0≤k ∧ k<Int.ofNat (shards.getD a.toNat default).shard_sizes.length) →
        (shards.getD a.toNat default).shard_sizes.getD k.toNat default>0)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (empty : Int.ofNat dims.length=0) (nontrivial : 1<Int.ofNat shards.length) :
    validate_non_overlapping_shards_metadata__error shards VeriPy.Error.value := by
  apply ValidationWitness shards 0 1 (by omega) (by omega) (by omega)
  apply PartitionOverlap shards dims 0 1 ranks positive part (by omega) (by omega)
  have nil : dims=[] := List.eq_nil_of_length_eq_zero (by simp only [VeriPy.ofNat_cast] at empty;omega)
  simp only [nil,List.not_mem_nil,false_implies,implies_true]

@[spec]
theorem validate_non_overlapping_shards_metadata__proof («shards» : (List «ShardMetadata»)) (__vp_h0 : (((Int.ofNat («shards»).length) ≤ (9223372036854775807 : Int)))) (__vp_h1 : (∀ «a» : Int, (0 ≤ «a» ∧ «a» < (Int.ofNat («shards»).length)) → ((((Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_offsets»).length) = (Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_sizes»).length))) ∧ (((Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_offsets»).length) = (Int.ofNat ((((«shards»).getD ((0 : Int)).toNat default)).«shard_offsets»).length)))))) (__vp_h2 : (∀ «a» : Int, (0 ≤ «a» ∧ «a» < (Int.ofNat («shards»).length)) → (∀ «k» : Int, (0 ≤ «k» ∧ «k» < (Int.ofNat ((((«shards»).getD («a»).toNat default)).«shard_sizes»).length)) → (((((((«shards»).getD («a»).toNat default)).«shard_sizes»).getD («k»).toNat default) > (0 : Int)))))) :
  ⦃⌜True⌝⦄ «validate_non_overlapping_shards_metadata» «shards» ⦃(fun __vp_result => ⌜(«validate_non_overlapping_shards_metadata__post» «shards» __vp_result)⌝, fun (__vp_error : VeriPy.Error) => ⌜(«validate_non_overlapping_shards_metadata__error» «shards» __vp_error)⌝, ())⦄ := by
  mvcgen [«validate_non_overlapping_shards_metadata», VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]
  all_goals try (veripy_loop_tag 141; exact (by exact (fun ⟨__vp_cursor, «sharded_dims», «__vp_index_141»⟩ => ⌜(«validate_non_overlapping_shards_metadata__inv_141» «shards» «sharded_dims» «__vp_index_141») ∧ «__vp_index_141» = Int.ofNat __vp_cursor.prefix.length⌝, fun __vp_error => ⌜(«validate_non_overlapping_shards_metadata__error» «shards» __vp_error)⌝, ())))
  all_goals try (veripy_loop_tag 144; exact (by
    veripy_cursor dim 141 0 0 0
    exact (fun ⟨cursor, dims, k⟩ => ⌜if cursor.suffix=[] then Partitioned shards dims (dim+1)
      else Partitioned shards dims dim ∧ SamePrefix shards dim (1+k) ∧ k=Int.ofNat cursor.prefix.length⌝,
      fun (_ : VeriPy.Error) => ⌜False⌝, ())))
  all_goals (
    try veripy_clear_aux
    try (simp only [VeriPy.loopTag, decide_eq_true_eq, WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals try veripy_continue_facts
    all_goals try veripy_project_facts
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals try veripy_fold_projections
    all_goals try (simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.not_ofNat_neg, if_true, if_false, Int.toNat_natCast] at *)
    all_goals try (first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega)
  )

  all_goals try (solve | apply ValidationTrivial; simp only [VeriPy.ofNat_cast];grind)
  all_goals try (solve | apply PartitionAdvanceAdd <;> first | assumption | omega)
  all_goals try (solve | exact PartitionEmpty shards)
  all_goals try (
    veripy_cursor dimension 141 0 0 0
    have db:=RangeCursor (Int.ofNat (shards.getD 0 default).shard_offsets.length) dimension _ _ (by assumption)
    veripy_cursor item 144 0 0 0
    have ib:=RangeFromCursor 1 (Int.ofNat shards.length) item _ _ (by assumption)
    have safe:=ValidationDimensionRaw shards item dimension (by exact __vp_h1) (by have h:=ib.2;omega) db.2
    dsimp only [dimension,item] at db ib safe
    simp only [VeriPy.ofNat_cast] at db ib safe
    grind only
  )

  all_goals try (
    veripy_cursor dimension 141 0 0 0
    have db:=RangeCursor (Int.ofNat (shards.getD 0 default).shard_offsets.length) dimension _ _ (by assumption)
    dsimp only [dimension] at db
    simp only [VeriPy.ofNat_cast] at db
  )
  try (case' vc57.step.post.success.left => solve | apply PartitionOuterStep <;> first | assumption | (simp only [VeriPy.ofNat_cast];omega))
  try (case' vc56.step.pre => solve | apply PartitionScanInitFromOuter <;> first | assumption | (simp only [VeriPy.ofNat_cast];omega))
  try (case' vc60.h => solve |
    intro x hx
    have nonempty : 0<(shards.length:Int) := by omega
    simp only [if_pos nonempty]
    simp
    split <;> simp_all
    all_goals rfl)
  try (case' vc82.isFalse.isFalse.isTrue.post.success.isFalse.isFalse.success.isFalse => solve | apply ValidationNDReturn shards <;> assumption)
  try (case' vc84.isFalse.isFalse.isFalse => solve | exfalso; apply ValidationFirstFailure shards <;> grind only)
  try (case' vc48.step.isTrue.isTrue.isTrue.isTrue.isFalse.isTrue.isTrue.isTrue.isFalse => solve |
    have base:=ValidationDimensionRaw shards 0 dimension (by exact __vp_h1) (by simp only [VeriPy.ofNat_cast];omega) (by simpa only [VeriPy.ofNat_cast] using db.2)
    dsimp only [dimension] at base
    simp only [VeriPy.ofNat_cast] at base
    grind only)

  try (case' vc61.isFalse.isFalse.isTrue.post.success.isTrue.success.isTrue => solve |
    exfalso
    apply ValidationAllZerosImpossible shards
    · exact __vp_h2
    · simp only [VeriPy.ofNat_cast];omega
    · grind only)
  try (case' vc47.step.isTrue.isTrue.isTrue.isTrue.isFalse.isTrue.isTrue.isTrue.isTrue.isFalse => solve |
    apply PartitionScanStep
    all_goals first | assumption | (simp only [VeriPy.ofNat_cast];omega) | (simp only [Read,VeriPy.ofNat_cast];grind only))

  all_goals try (have finalPart:=PartitionFinal shards _ _ (by assumption) (by assumption))
  try (case' vc77.__vp_h4 => solve |
    right;exact PartitionDimensions shards _ finalPart)
  try (case' vc66.__vp_h0 => solve |
    apply Validation1DPre shards _ __vp_h1 __vp_h2 finalPart
    simp only [VeriPy.ofNat_cast];omega)
  try (case' vc62.isFalse.isFalse.isTrue.post.success.isTrue.success.isFalse.isTrue.isTrue.isTrue => solve |
    apply ValidationNoDims shards _ __vp_h1 __vp_h2 finalPart
    all_goals simp only [VeriPy.ofNat_cast];omega)
  try (case' vc78.isFalse.isFalse.isTrue.post.success.isFalse.isFalse.success.isTrue.h_1.isTrue.isTrue => solve |
    apply ValidationNDWitness shards _ _ _ __vp_h1 <;> assumption)
  try (case' vc67.isFalse.isFalse.isTrue.post.success.isFalse.isTrue.isTrue.success.isTrue.h_1.isTrue.isTrue => solve |
    apply Validation1DWitness shards _ _ _ __vp_h1 __vp_h2 finalPart
    all_goals first | assumption | (simp only [VeriPy.ofNat_cast];omega))
  try (case' vc71.isFalse.isFalse.isTrue.post.success.isFalse.isTrue.isTrue.success.isFalse => solve |
    apply Validation1DReturn shards _ _ __vp_h1 finalPart
    all_goals first | assumption | (simp only [VeriPy.ofNat_cast];omega))
  all_goals try (solve |
    have safe:=ValidationPairAccess shards _ _ (by assumption) (by assumption)
    simp only [VeriPy.ofNat_cast] at safe
    grind only)

theorem NoReturnedOverlap (shards : List ShardMetadata) (dims : List Int) (value : Option (Int × Int))
    (ranks : Ranks shards)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (nonempty : 0<Int.ofNat dims.length)
    (post : _find_1d_overlapping_shards__post shards (dims.getD 0 default) value)
    (none : ¬value≠Option.none) : validate_non_overlapping_shards_metadata__post shards () := by
  have equal : value=Option.none := Classical.not_not.mp none
  subst value
  exact Validation1DNone shards dims ranks part nonempty post


theorem ReturnedOverlap (shards : List ShardMetadata) (dims : List Int) (value : Option (Int × Int)) (p : Int × Int)
    (ranks : Ranks shards)
    (positive : ∀ a : Int, (0≤a ∧ a<Int.ofNat shards.length) → ∀ k : Int,
      (0≤k ∧ k<Int.ofNat (shards.getD a.toNat default).shard_sizes.length) →
        (shards.getD a.toNat default).shard_sizes.getD k.toNat default>0)
    (part : Partitioned shards dims (Int.ofNat (Read shards 0).shard_offsets.length))
    (length : Int.ofNat dims.length=1)
    (post : _find_1d_overlapping_shards__post shards (dims.getD 0 default) value)
    (some : value=Option.some p) :
    validate_non_overlapping_shards_metadata__error shards VeriPy.Error.value := by
  subst value
  have bounds:=post.1.resolve_left (by simp)
  simp only [Option.getD_some] at bounds
  have overlap:=post.2.1.resolve_left (by simp)
  apply ValidationWitness shards p.1 p.2 bounds.1 bounds.2.1 bounds.2.2
  apply PartitionOverlap shards dims p.1 p.2 ranks positive part bounds.1 bounds.2.1
  intro d hd
  have singleton : dims=[dims.getD 0 default] := by
    cases dims with
    | nil => simp only [List.length_nil,VeriPy.ofNat_cast] at length;omega
    | cons x xs =>
      have empty : xs=[] := by simp only [List.length_cons,VeriPy.ofNat_cast] at length;exact List.eq_nil_of_length_eq_zero (by omega)
      subst xs;rfl
  rw [singleton] at hd
  have equal:=List.mem_singleton.mp hd
  subst d
  simpa only [Read,Option.getD_some] using overlap


