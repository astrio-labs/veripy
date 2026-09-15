// Defined predicates and checked lemmas for the unchanged PyTorch sweep.
ghost predicate ShardsOverlap(a: VRecShardMetadata, b: VRecShardMetadata)
{
  |a.vfieldshard_offsets| == |a.vfieldshard_sizes| == |b.vfieldshard_offsets| == |b.vfieldshard_sizes| &&
  (forall t :: 0 <= t < |a.vfieldshard_offsets| ==> a.vfieldshard_offsets[t] < b.vfieldshard_offsets[t] + b.vfieldshard_sizes[t] && b.vfieldshard_offsets[t] < a.vfieldshard_offsets[t] + a.vfieldshard_sizes[t])
}
ghost predicate SweepDomain(s: seq<VRecShardMetadata>, order: seq<int>, d: int)
{
  |s| > 0 && 0 <= d < |s[0].vfieldshard_offsets| &&
  (forall a :: 0 <= a < |s| ==> |s[a].vfieldshard_offsets| == |s[a].vfieldshard_sizes| && |s[a].vfieldshard_offsets| == |s[0].vfieldshard_offsets|) &&
  |order| == |s| &&
  (forall a :: 0 <= a < |order| ==> 0 <= order[a] < |s|) &&
  (forall v :: v in order <==> 0 <= v < |s|) &&
  (forall a,b :: 0 <= a < b < |order| ==> order[a] != order[b] && s[order[a]].vfieldshard_offsets[d] <= s[order[b]].vfieldshard_offsets[d])
}
ghost predicate ActiveState(s: seq<VRecShardMetadata>, order: seq<int>, k: int, d: int, active: seq<(int,int)>)
  requires SweepDomain(s,order,d)
  requires 0 <= k <= |order|
{
  (forall v :: v in active ==> 0 <= v.1 < |s| && v.1 in order[..k] && v.0 == s[v.1].vfieldshard_offsets[d] + s[v.1].vfieldshard_sizes[d]) &&
  (forall a,b :: 0 <= a < b < |active| ==> PyLex2(active[a],active[b])) &&
  (forall a :: 0 <= a < k ==> k < |order| && s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d] > s[order[k]].vfieldshard_offsets[d] ==> (s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d],order[a]) in active)
}
ghost predicate ProcessedDisjoint(s: seq<VRecShardMetadata>, order: seq<int>, k: int)
  requires 0 <= k <= |order|
  requires forall a :: 0 <= a < |order| ==> 0 <= order[a] < |s|
{
  forall a,b :: 0 <= a < b < k ==> !ShardsOverlap(s[order[a]],s[order[b]])
}
ghost predicate Scanned(s: seq<VRecShardMetadata>, idx: int, active: seq<(int,int)>, k: int)
  requires 0 <= idx < |s|
  requires 0 <= k <= |active|
  requires forall v :: v in active ==> 0 <= v.1 < |s|
{
  forall a :: 0 <= a < k ==> !ShardsOverlap(s[idx],s[active[a].1])
}
lemma OverlapSymmetric(a: VRecShardMetadata, b: VRecShardMetadata)
  ensures ShardsOverlap(a,b) == ShardsOverlap(b,a)
{
  if ShardsOverlap(a,b) {
    assert |a.vfieldshard_offsets| == |b.vfieldshard_offsets|;
  }
  if ShardsOverlap(b,a) {
    assert |a.vfieldshard_offsets| == |b.vfieldshard_offsets|;
  }
}
lemma ActiveSuffix(s: seq<VRecShardMetadata>, order: seq<int>, k: int, d: int, active: seq<(int,int)>, c: int)
  requires SweepDomain(s,order,d)
  requires 0 <= k < |order|
  requires ActiveState(s,order,k,d,active)
  requires 0 <= c <= |active|
  requires forall a :: 0 <= a < c ==> active[a].0 <= s[order[k]].vfieldshard_offsets[d]
  ensures ActiveState(s,order,k,d,active[c..])
{
  forall v | v in active[c..]
    ensures 0 <= v.1 < |s| && v.1 in order[..k] && v.0 == s[v.1].vfieldshard_offsets[d] + s[v.1].vfieldshard_sizes[d]
  { assert v in active; }
  forall a | 0 <= a < k && s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d] > s[order[k]].vfieldshard_offsets[d]
    ensures (s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d],order[a]) in active[c..]
  {
    var row := (s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d],order[a]);
    assert row in active;
    var q :| 0 <= q < |active| && active[q] == row;
    assert q >= c;
  }
}
lemma ActiveInsert(s: seq<VRecShardMetadata>, order: seq<int>, k: int, d: int, active: seq<(int,int)>)
  requires SweepDomain(s,order,d)
  requires 0 <= k < |order|
  requires ActiveState(s,order,k,d,active)
  ensures ActiveState(s,order,k+1,d,PyInsert2((s[order[k]].vfieldshard_offsets[d] + s[order[k]].vfieldshard_sizes[d],order[k]),active))
{
  var row := (s[order[k]].vfieldshard_offsets[d] + s[order[k]].vfieldshard_sizes[d],order[k]);
  PyInsert2Facts(row,active);
  var added := PyInsert2(row,active);
  forall v | v in added
    ensures 0 <= v.1 < |s| && v.1 in order[..k+1] && v.0 == s[v.1].vfieldshard_offsets[d] + s[v.1].vfieldshard_sizes[d]
  {
    if v != row { assert v in active; }
  }
  forall a | 0 <= a < k+1 && k+1 < |order| && s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d] > s[order[k+1]].vfieldshard_offsets[d]
    ensures (s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d],order[a]) in added
  {
    if a < k {
      assert s[order[k]].vfieldshard_offsets[d] <= s[order[k+1]].vfieldshard_offsets[d];
      assert (s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d],order[a]) in active;
    }
  }
}
lemma ScannedStep(s: seq<VRecShardMetadata>, idx: int, active: seq<(int,int)>, k: int)
  requires 0 <= idx < |s|
  requires 0 <= k < |active|
  requires forall v :: v in active ==> 0 <= v.1 < |s|
  requires Scanned(s,idx,active,k)
  ensures ShardsOverlap(s[idx],s[active[k].1]) || Scanned(s,idx,active,k+1)
{
  if !ShardsOverlap(s[idx],s[active[k].1]) {
    forall a | 0 <= a < k+1 ensures !ShardsOverlap(s[idx],s[active[a].1]) {
      if a < k { assert !ShardsOverlap(s[idx],s[active[a].1]); }
    }
  }
}
lemma SweepStep(s: seq<VRecShardMetadata>, order: seq<int>, k: int, d: int, active: seq<(int,int)>)
  requires SweepDomain(s,order,d)
  requires 0 <= k < |order|
  requires ActiveState(s,order,k,d,active)
  requires ProcessedDisjoint(s,order,k)
  requires Scanned(s,order[k],active,|active|)
  ensures ProcessedDisjoint(s,order,k+1)
{
  forall a,b | 0 <= a < b < k+1 ensures !ShardsOverlap(s[order[a]],s[order[b]]) {
    if b < k { assert !ShardsOverlap(s[order[a]],s[order[b]]); }
    else {
      assert b == k;
      if s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d] <= s[order[k]].vfieldshard_offsets[d] {
        assert 0 <= d < |s[order[a]].vfieldshard_offsets|;
      } else {
        var row := (s[order[a]].vfieldshard_offsets[d] + s[order[a]].vfieldshard_sizes[d],order[a]);
        assert row in active;
        var q :| 0 <= q < |active| && active[q] == row;
        assert !ShardsOverlap(s[order[k]],s[active[q].1]);
        OverlapSymmetric(s[order[a]],s[order[k]]);
      }
    }
  }
}
lemma AllPairs(s: seq<VRecShardMetadata>, order: seq<int>, d: int, overlap: bool)
  requires SweepDomain(s,order,d)
  requires ProcessedDisjoint(s,order,|order|)
  requires overlap ==> (exists i,j :: 0 <= i < |s| && 0 <= j < |s| && i != j && ShardsOverlap(s[i],s[j]))
  ensures !overlap
{
  if overlap {
    var i,j :| 0 <= i < |s| && 0 <= j < |s| && i != j && ShardsOverlap(s[i],s[j]);
    assert ShardsOverlap(s[i],s[j]);
    assert i in order && j in order;
    var a :| 0 <= a < |order| && order[a] == i;
    var b :| 0 <= b < |order| && order[b] == j;
    assert a != b;
    if a < b { assert !ShardsOverlap(s[order[a]],s[order[b]]); }
    else { OverlapSymmetric(s[i],s[j]); assert !ShardsOverlap(s[order[b]],s[order[a]]); }
  }
}

lemma SelectedDimension(s: seq<VRecShardMetadata>, dims: seq<int>, k: int)
  requires |s| > 0
  requires 0 <= k < |dims|
  requires forall a :: 0 <= a < |s| ==> |s[a].vfieldshard_offsets| == |s[a].vfieldshard_sizes| && |s[a].vfieldshard_offsets| == |s[0].vfieldshard_offsets|
  requires forall t :: 0 <= t < |dims| ==> 0 <= dims[t] < |s[0].vfieldshard_offsets|
  ensures forall a :: 0 <= a < |s| ==> 0 <= dims[k] < |s[a].vfieldshard_offsets| && |s[a].vfieldshard_sizes| == |s[a].vfieldshard_offsets|
{
  assert 0 <= dims[k] < |s[0].vfieldshard_offsets|;
  forall a | 0 <= a < |s| ensures 0 <= dims[k] < |s[a].vfieldshard_offsets| && |s[a].vfieldshard_sizes| == |s[a].vfieldshard_offsets| {
    assert |s[a].vfieldshard_offsets| == |s[0].vfieldshard_offsets|;
  }
}

lemma SearchOverlapWitness(shards: seq<VRecShardMetadata>, sharded_dims: seq<int>)
  requires (|shards| <= 9223372036854775807)
  requires (((|shards| <= 1)) || ((|sharded_dims| > 0)))
  requires (forall a :: (0 <= a < |shards|) ==> ((((|(shards[a]).vfieldshard_offsets| == |(shards[a]).vfieldshard_sizes|)) && ((|(shards[a]).vfieldshard_offsets| == |(shards[0]).vfieldshard_offsets|)))))
  requires (forall a, k :: (0 <= a < |shards| && 0 <= k < |(shards[a]).vfieldshard_sizes|) ==> (((shards[a]).vfieldshard_sizes[k] > 0)))
  requires (((|shards| == 0)) || ((forall k :: (0 <= k < |sharded_dims|) ==> ((0 <= sharded_dims[k] && sharded_dims[k] < |(shards[0]).vfieldshard_offsets|)))))
  ensures VSpecpy_find_nd_overlapping_shards_(sharded_dims,shards) ==> (exists i,j :: 0 <= i < |shards| && 0 <= j < |shards| && i != j && ShardsOverlap(shards[i],shards[j]))
{
  if VSpecpy_find_nd_overlapping_shards_(sharded_dims,shards) {
    var a,b :| 0 <= a < |shards| && 0 <= b < |shards| && a != b && VSpecpy_find_nd_overlapping_shards(a,b,sharded_dims,shards);
    assert ShardsOverlap(shards[a],shards[b]);
    assert exists i,j :: 0 <= i < |shards| && 0 <= j < |shards| && i != j && ShardsOverlap(shards[i],shards[j]);
  }
}
