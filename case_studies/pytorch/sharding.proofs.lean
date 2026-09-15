-- VERIPY LIBRARY arithmetic
theorem get_split_size__proof (dim_size chunks : Int) (hd : dim_size≥0) (hc : chunks>0) :
    (dim_size+chunks-1).fdiv chunks≥0 ∧
    ((dim_size+chunks-1).fdiv chunks-1)*chunks<dim_size ∧
    dim_size≤(dim_size+chunks-1).fdiv chunks*chunks := by
  have facts:=FloorDivFacts (dim_size+chunks-1) chunks
  have bound:=facts.2.1 hc
  have nonnegative : 0≤(dim_size+chunks-1).fdiv chunks := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    exact Int.ediv_nonneg (by omega) (by omega)
  simp only [Int.sub_mul,Int.one_mul]
  omega

theorem get_chunked_dim_size__proof (dim_size split_size idx : Int) (hd : dim_size≥0) (hs : split_size≥0) (hi : idx≥0) :
    (0≤max (min dim_size (split_size*(idx+1))-split_size*idx) 0 ∧ max (min dim_size (split_size*(idx+1))-split_size*idx) 0≤split_size) ∧
    max (min dim_size (split_size*(idx+1))-split_size*idx) 0≤dim_size ∧
    (¬split_size*idx≥dim_size ∨ max (min dim_size (split_size*(idx+1))-split_size*idx) 0=0) ∧
    (¬split_size*(idx+1)≤dim_size ∨ max (min dim_size (split_size*(idx+1))-split_size*idx) 0=split_size) ∧
    (¬(split_size*idx<dim_size ∧ dim_size<split_size*(idx+1)) ∨ max (min dim_size (split_size*(idx+1))-split_size*idx) 0=dim_size-split_size*idx) := by
  have product:=Int.mul_nonneg hs hi
  simp only [Int.mul_add,Int.mul_one]
  omega
