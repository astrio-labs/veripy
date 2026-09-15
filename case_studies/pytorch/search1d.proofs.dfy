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
