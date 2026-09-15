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
lemma UniqueCount(s: seq<(int,int,int)>, k: int)
  requires 0 <= k < |s|
  requires forall i,j :: 0 <= i < j < |s| ==> s[i].2 != s[j].2
  ensures PyCount3(s,s[k]) == 1
  decreases |s|
{
  assert s == [s[0]] + s[1..];
  if k == 0 {
    assert s[0] !in s[1..];
  } else {
    UniqueCount(s[1..],k-1);
  }
}

lemma DuplicateCount(s: seq<(int,int,int)>, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] == s[j]
  ensures PyCount3(s,s[i]) >= 2
{
  assert s == s[..j] + [s[j]] + s[j+1..];
  assert s[i] in s[..j];
}

lemma PermutedRows(a: seq<(int,int,int)>, b: seq<(int,int,int)>)
  requires PyPerm3(a,b)
  requires forall i :: 0 <= i < |b| ==> b[i].2 == i
  ensures |a| == |b|
  ensures forall i :: 0 <= i < |a| ==> 0 <= a[i].2 < |b| && a[i] == b[a[i].2]
  ensures forall i,j :: 0 <= i < j < |a| ==> a[i].2 != a[j].2
{
  PyPerm3Facts(a,b);
  forall i | 0 <= i < |a| ensures 0 <= a[i].2 < |b| && a[i] == b[a[i].2] {
    assert a[i] in a;
    assert a[i] in b;
    var k :| 0 <= k < |b| && b[k] == a[i];
  }
  forall i,j | 0 <= i < j < |a| ensures a[i].2 != a[j].2 {
    if a[i].2 == a[j].2 {
      assert a[i] == a[j];
      UniqueCount(b,a[i].2);
      DuplicateCount(a,i,j);
    }
  }

}

lemma NoAdjacentOverlap(a: seq<(int,int,int)>)
  requires forall i,j :: 0 <= i < j < |a| ==> a[i].0 <= a[j].0
  requires forall i :: 0 <= i < |a|-1 ==> a[i].1 < a[i+1].0
  ensures forall i,j :: 0 <= i < j < |a| ==> a[i].1 < a[j].0
{
  forall i,j | 0 <= i < j < |a| ensures a[i].1 < a[j].0 {
    if j > i+1 { assert a[i+1].0 <= a[j].0; }
  }
}

lemma PermutedDisjoint(a: seq<(int,int,int)>, b: seq<(int,int,int)>)
  requires PyPerm3(a,b)
  requires forall i :: 0 <= i < |b| ==> b[i].2 == i
  requires forall i,j :: 0 <= i < j < |a| ==> a[i].1 < a[j].0
  ensures forall i,j :: 0 <= i < |b| && 0 <= j < |b| && i != j ==> b[i].1 < b[j].0 || b[j].1 < b[i].0
{
  PermutedRows(a,b);
  PyPerm3Facts(a,b);
  forall i,j | 0 <= i < |b| && 0 <= j < |b| && i != j ensures b[i].1 < b[j].0 || b[j].1 < b[i].0 {
    assert b[i] in b;
    assert b[j] in b;
    assert b[i] in a;
    assert b[j] in a;
    var p :| 0 <= p < |a| && a[p] == b[i];
    var q :| 0 <= q < |a| && a[q] == b[j];
    assert p != q;
  }
}

lemma ShardDisjoint(shards: seq<VRecShardMetadata>, dim: int, b: seq<(int,int,int)>)
  requires forall i :: 0 <= i < |shards| ==> 0 <= dim < |shards[i].vfieldshard_offsets| && |shards[i].vfieldshard_offsets| == |shards[i].vfieldshard_sizes|
  requires |b| == |shards|
  requires forall i :: 0 <= i < |b| ==> b[i] == (shards[i].vfieldshard_offsets[dim], shards[i].vfieldshard_offsets[dim] + shards[i].vfieldshard_sizes[dim] - 1, i)
  requires forall i,j :: 0 <= i < |b| && 0 <= j < |b| && i != j ==> b[i].1 < b[j].0 || b[j].1 < b[i].0
  ensures forall i :: 0 <= i < |shards| ==> (forall j :: 0 <= j < |shards| ==> i == j || shards[i].vfieldshard_offsets[dim] + shards[i].vfieldshard_sizes[dim] <= shards[j].vfieldshard_offsets[dim] || shards[j].vfieldshard_offsets[dim] + shards[j].vfieldshard_sizes[dim] <= shards[i].vfieldshard_offsets[dim])
{
  forall i | 0 <= i < |shards|
    ensures forall j :: 0 <= j < |shards| ==> i == j || shards[i].vfieldshard_offsets[dim] + shards[i].vfieldshard_sizes[dim] <= shards[j].vfieldshard_offsets[dim] || shards[j].vfieldshard_offsets[dim] + shards[j].vfieldshard_sizes[dim] <= shards[i].vfieldshard_offsets[dim]
  {
    forall j | 0 <= j < |shards|
      ensures i == j || shards[i].vfieldshard_offsets[dim] + shards[i].vfieldshard_sizes[dim] <= shards[j].vfieldshard_offsets[dim] || shards[j].vfieldshard_offsets[dim] + shards[j].vfieldshard_sizes[dim] <= shards[i].vfieldshard_offsets[dim]
    { if i != j { assert b[i].1 < b[j].0 || b[j].1 < b[i].0; } }
  }
}

lemma PositiveVolume(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures PyProd(s) > 0
  decreases |s|
{
  if |s| > 0 { PositiveVolume(s[..|s|-1]); }
}

ghost predicate MetadataShape(s: seq<VRecShardMetadata>)
{
  |s| > 0 && (forall a :: 0 <= a < |s| ==> |s[a].vfieldshard_offsets| == |s[a].vfieldshard_sizes| && |s[a].vfieldshard_offsets| == |s[0].vfieldshard_offsets|) &&
  (forall a,k :: 0 <= a < |s| && 0 <= k < |s[a].vfieldshard_sizes| ==> s[a].vfieldshard_sizes[k] > 0)
}
ghost predicate Partitioned(s: seq<VRecShardMetadata>, dims: seq<int>, upto: int)
  requires MetadataShape(s)
  requires 0 <= upto <= |s[0].vfieldshard_offsets|
{
  (forall k :: 0 <= k < |dims| ==> 0 <= dims[k] < upto) &&
  (forall d :: 0 <= d < upto ==> d !in dims ==> (forall a :: 0 <= a < |s| ==> s[a].vfieldshard_offsets[d] == s[0].vfieldshard_offsets[d] && s[a].vfieldshard_sizes[d] == s[0].vfieldshard_sizes[d]))
}
ghost predicate SamePrefix(s: seq<VRecShardMetadata>, d: int, k: int)
  requires MetadataShape(s)
  requires 0 <= d < |s[0].vfieldshard_offsets|
  requires 1 <= k <= |s|
{
  forall a :: 0 <= a < k ==> s[a].vfieldshard_offsets[d] == s[0].vfieldshard_offsets[d] && s[a].vfieldshard_sizes[d] == s[0].vfieldshard_sizes[d]
}
lemma PartitionAdvance(s: seq<VRecShardMetadata>, dims: seq<int>, d: int)
  requires MetadataShape(s)
  requires 0 <= d < |s[0].vfieldshard_offsets|
  requires Partitioned(s,dims,d)
  ensures Partitioned(s,dims+[d],d+1)
  ensures SamePrefix(s,d,|s|) ==> Partitioned(s,dims,d+1)
{
  forall q | 0 <= q < d+1 && q !in dims+[d]
    ensures forall a :: 0 <= a < |s| ==> s[a].vfieldshard_offsets[q] == s[0].vfieldshard_offsets[q] && s[a].vfieldshard_sizes[q] == s[0].vfieldshard_sizes[q]
  { assert q < d && q !in dims; }
  if SamePrefix(s,d,|s|) {
    forall q | 0 <= q < d+1 && q !in dims
      ensures forall a :: 0 <= a < |s| ==> s[a].vfieldshard_offsets[q] == s[0].vfieldshard_offsets[q] && s[a].vfieldshard_sizes[q] == s[0].vfieldshard_sizes[q]
    { if q < d { assert q !in dims; } }
  }
}

lemma ReturnedOverlap(s: seq<VRecShardMetadata>, dims: seq<int>, pair: PyOpt<(int,int)>)
  requires MetadataShape(s)
  requires |s| <= 9223372036854775807
  requires Partitioned(s,dims,|s[0].vfieldshard_offsets|)
  requires pair.PySome?
  requires 0 <= pair.v.0 < |s| && 0 <= pair.v.1 < |s| && pair.v.0 != pair.v.1
  requires |dims| == 1 ==> s[pair.v.0].vfieldshard_offsets[dims[0]] < s[pair.v.1].vfieldshard_offsets[dims[0]] + s[pair.v.1].vfieldshard_sizes[dims[0]] && s[pair.v.1].vfieldshard_offsets[dims[0]] < s[pair.v.0].vfieldshard_offsets[dims[0]] + s[pair.v.0].vfieldshard_sizes[dims[0]]
  requires |dims| > 1 ==> !(exists d :: 0 <= d < |s[PyIndex(pair.v.0,|s|)].vfieldshard_offsets| && (s[PyIndex(pair.v.0,|s|)].vfieldshard_offsets[d] + s[PyIndex(pair.v.0,|s|)].vfieldshard_sizes[d] <= s[PyIndex(pair.v.1,|s|)].vfieldshard_offsets[d] || s[PyIndex(pair.v.1,|s|)].vfieldshard_offsets[d] + s[PyIndex(pair.v.1,|s|)].vfieldshard_sizes[d] <= s[PyIndex(pair.v.0,|s|)].vfieldshard_offsets[d]))
  ensures VSpecvalidate_non_overlapping_shards_metadata_(s)
{
  var a,b := pair.v.0,pair.v.1;
  if |dims| <= 1 {
    forall d | 0 <= d < |s[a].vfieldshard_offsets|
      ensures s[a].vfieldshard_offsets[d] < s[b].vfieldshard_offsets[d] + s[b].vfieldshard_sizes[d] && s[b].vfieldshard_offsets[d] < s[a].vfieldshard_offsets[d] + s[a].vfieldshard_sizes[d]
    {
      if d in dims {
        assert |dims| == 1 && d == dims[0];
      } else {
        assert s[a].vfieldshard_offsets[d] == s[0].vfieldshard_offsets[d];
        assert s[b].vfieldshard_offsets[d] == s[0].vfieldshard_offsets[d];
        assert s[a].vfieldshard_sizes[d] > 0 && s[b].vfieldshard_sizes[d] > 0;
      }
    }
  }
  if |dims| > 1 {
    assert PyIndex(a,|s|) == a && PyIndex(b,|s|) == b;
    forall d | 0 <= d < |s[a].vfieldshard_offsets|
      ensures s[a].vfieldshard_offsets[d] < s[b].vfieldshard_offsets[d] + s[b].vfieldshard_sizes[d] && s[b].vfieldshard_offsets[d] < s[a].vfieldshard_offsets[d] + s[a].vfieldshard_sizes[d]
    {
      assert !(s[PyIndex(a,|s|)].vfieldshard_offsets[d] + s[PyIndex(a,|s|)].vfieldshard_sizes[d] <= s[PyIndex(b,|s|)].vfieldshard_offsets[d] || s[PyIndex(b,|s|)].vfieldshard_offsets[d] + s[PyIndex(b,|s|)].vfieldshard_sizes[d] <= s[PyIndex(a,|s|)].vfieldshard_offsets[d]);
    }
  }
  assert ShardsOverlap(s[a],s[b]);
  if a < b {
    assert VSpecvalidate_non_overlapping_shards_metadata(a,b,s);
  } else {
    OverlapSymmetric(s[a],s[b]);
    assert VSpecvalidate_non_overlapping_shards_metadata(b,a,s);
  }
  assert VSpecvalidate_non_overlapping_shards_metadata_(s);
}

lemma NoReturnedOverlap(s: seq<VRecShardMetadata>, dims: seq<int>, pair: PyOpt<(int,int)>)
  requires MetadataShape(s)
  requires 1 < |s| <= 9223372036854775807
  requires Partitioned(s,dims,|s[0].vfieldshard_offsets|)
  requires |dims| == 0 ==> pair.PySome?
  requires |dims| == 1 && pair.PyNone? ==> (forall a,b :: 0 <= a < |s| && 0 <= b < |s| ==> a == b || s[a].vfieldshard_offsets[dims[0]] + s[a].vfieldshard_sizes[dims[0]] <= s[b].vfieldshard_offsets[dims[0]] || s[b].vfieldshard_offsets[dims[0]] + s[b].vfieldshard_sizes[dims[0]] <= s[a].vfieldshard_offsets[dims[0]])
  requires |dims| > 1 && pair.PyNone? ==> !VSpecpy_find_nd_overlapping_shards_(dims,s)
  ensures pair.PyNone? ==> !VSpecvalidate_non_overlapping_shards_metadata_(s)
{
  if pair.PyNone? && VSpecvalidate_non_overlapping_shards_metadata_(s) {
    var a,b :| 0 <= a < |s| && a+1 <= b < |s| && VSpecvalidate_non_overlapping_shards_metadata(a,b,s);
    assert ShardsOverlap(s[a],s[b]);
    if |dims| == 1 {
      var d := dims[0];
      assert s[a].vfieldshard_offsets[d] < s[b].vfieldshard_offsets[d] + s[b].vfieldshard_sizes[d];
      assert s[b].vfieldshard_offsets[d] < s[a].vfieldshard_offsets[d] + s[a].vfieldshard_sizes[d];
    } else {
      assert VSpecpy_find_nd_overlapping_shards(a,b,dims,s);
      assert VSpecpy_find_nd_overlapping_shards_(dims,s);
    }
  }
}
