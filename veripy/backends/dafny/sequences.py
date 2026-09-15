"""Exact lexicographic sorting of integer pairs and triples, with checked facts."""

PREAMBLE = r'''
predicate PyLex2(a: (int, int), b: (int, int)) { (a.0 < b.0) || (a.0 == b.0 && a.1 <= b.1) }
function PyInsert2(x: (int, int), s: seq<(int, int)>): seq<(int, int)>
  decreases |s|
{ if |s| == 0 then [x] else if PyLex2(x,s[0]) then [x] + s else [s[0]] + PyInsert2(x,s[1..]) }
function PySorted2(s: seq<(int, int)>): seq<(int, int)>
  decreases |s|
{ if |s| == 0 then [] else PyInsert2(s[0], PySorted2(s[1..])) }
lemma PyInsert2Facts(x: (int, int), s: seq<(int, int)>)
  requires forall i,j :: 0 <= i < j < |s| ==> PyLex2(s[i], s[j])
  ensures |PyInsert2(x,s)| == |s| + 1
  ensures forall v :: v in PyInsert2(x,s) <==> v == x || v in s
  ensures multiset(PyInsert2(x,s)) == multiset(s) + multiset{x}
  ensures forall i,j :: 0 <= i < j < |PyInsert2(x,s)| ==> PyLex2(PyInsert2(x,s)[i], PyInsert2(x,s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    if !PyLex2(x,s[0]) {
      PyInsert2Facts(x,s[1..]);
      var tail := PyInsert2(x,s[1..]);
      forall k | 0 <= k < |tail| ensures PyLex2(s[0],tail[k]) {
        if tail[k] != x {
          assert tail[k] in tail;
          assert multiset(tail)[tail[k]] > 0;
          assert multiset{x}[tail[k]] == 0;
          assert tail[k] in s[1..];
          var j :| 0 <= j < |s[1..]| && s[1..][j] == tail[k];
          assert PyLex2(s[0],s[j+1]);
        }
      }
    } else {
      forall j | 0 <= j < |s| ensures PyLex2(x,s[j]) {
        if j > 0 { assert PyLex2(s[0],s[j]); }
      }
    }
  }
}
lemma PySorted2Facts(s: seq<(int, int)>)
  ensures |PySorted2(s)| == |s|
  ensures forall v :: v in PySorted2(s) <==> v in s
  ensures multiset(PySorted2(s)) == multiset(s)
  ensures forall i,j :: 0 <= i < j < |PySorted2(s)| ==> PyLex2(PySorted2(s)[i], PySorted2(s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    PySorted2Facts(s[1..]);
    PyInsert2Facts(s[0],PySorted2(s[1..]));
  }
}
predicate PyLex3(a: (int, int, int), b: (int, int, int)) { (a.0 < b.0) || (a.0 == b.0 && a.1 < b.1) || (a.0 == b.0 && a.1 == b.1 && a.2 <= b.2) }
function PyInsert3(x: (int, int, int), s: seq<(int, int, int)>): seq<(int, int, int)>
  decreases |s|
{ if |s| == 0 then [x] else if PyLex3(x,s[0]) then [x] + s else [s[0]] + PyInsert3(x,s[1..]) }
function PySorted3(s: seq<(int, int, int)>): seq<(int, int, int)>
  decreases |s|
{ if |s| == 0 then [] else PyInsert3(s[0], PySorted3(s[1..])) }
lemma PyInsert3Facts(x: (int, int, int), s: seq<(int, int, int)>)
  requires forall i,j :: 0 <= i < j < |s| ==> PyLex3(s[i], s[j])
  ensures |PyInsert3(x,s)| == |s| + 1
  ensures forall v :: v in PyInsert3(x,s) <==> v == x || v in s
  ensures multiset(PyInsert3(x,s)) == multiset(s) + multiset{x}
  ensures forall i,j :: 0 <= i < j < |PyInsert3(x,s)| ==> PyLex3(PyInsert3(x,s)[i], PyInsert3(x,s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    if !PyLex3(x,s[0]) {
      PyInsert3Facts(x,s[1..]);
      var tail := PyInsert3(x,s[1..]);
      forall k | 0 <= k < |tail| ensures PyLex3(s[0],tail[k]) {
        if tail[k] != x {
          assert tail[k] in tail;
          assert multiset(tail)[tail[k]] > 0;
          assert multiset{x}[tail[k]] == 0;
          assert tail[k] in s[1..];
          var j :| 0 <= j < |s[1..]| && s[1..][j] == tail[k];
          assert PyLex3(s[0],s[j+1]);
        }
      }
    } else {
      forall j | 0 <= j < |s| ensures PyLex3(x,s[j]) {
        if j > 0 { assert PyLex3(s[0],s[j]); }
      }
    }
  }
}
lemma PySorted3Facts(s: seq<(int, int, int)>)
  ensures |PySorted3(s)| == |s|
  ensures forall v :: v in PySorted3(s) <==> v in s
  ensures multiset(PySorted3(s)) == multiset(s)
  ensures forall i,j :: 0 <= i < j < |PySorted3(s)| ==> PyLex3(PySorted3(s)[i], PySorted3(s)[j])
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    PySorted3Facts(s[1..]);
    PyInsert3Facts(s[0],PySorted3(s[1..]));
  }
}
'''

PREAMBLE += r'''
predicate PyPerm3(a: seq<(int,int,int)>, b: seq<(int,int,int)>) { multiset(a) == multiset(b) }
function PyCount3(s: seq<(int,int,int)>, x: (int,int,int)): nat { multiset(s)[x] }
'''

PREAMBLE += r'''
lemma PyPerm3Facts(a: seq<(int,int,int)>, b: seq<(int,int,int)>)
  requires PyPerm3(a,b)
  ensures |a| == |b|
  ensures forall x :: x in a <==> x in b
  ensures forall x :: PyCount3(a,x) == PyCount3(b,x)
{
  assert multiset(a) == multiset(b);
  assert |a| == |multiset(a)|;
  assert |b| == |multiset(b)|;
  forall x ensures x in a <==> x in b {
    assert (x in a) == (multiset(a)[x] > 0);
    assert (x in b) == (multiset(b)[x] > 0);
  }
}
'''

PREAMBLE += r'''
function PyLexSeq(a: seq<int>, b: seq<int>): bool
  decreases |a| + |b|
{ if |a| == 0 then true else if |b| == 0 then false else if a[0] < b[0] then true else if a[0] > b[0] then false else PyLexSeq(a[1..],b[1..]) }
function PyInsertIndex(x: int, s: seq<int>, keys: seq<seq<int>>): seq<int>
  requires 0 <= x < |keys|
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < |keys|
  ensures forall v :: v in PyInsertIndex(x,s,keys) <==> v == x || v in s
  decreases |s|
{ if |s| == 0 then [x] else if PyLexSeq(keys[x],keys[s[0]]) then [x]+s else [s[0]]+PyInsertIndex(x,s[1..],keys) }
lemma PyInsertIndexBounds(x: int, s: seq<int>, keys: seq<seq<int>>, lower: int)
  requires 0 <= lower <= x < |keys|
  requires forall i :: 0 <= i < |s| ==> lower <= s[i] < |keys|
  ensures forall i :: 0 <= i < |PyInsertIndex(x,s,keys)| ==> lower <= PyInsertIndex(x,s,keys)[i] < |keys|
{
  var r := PyInsertIndex(x,s,keys);
  forall i | 0 <= i < |r| ensures lower <= r[i] < |keys| {
    assert r[i] in r;
    if r[i] != x {
      assert r[i] in s;
      var j :| 0 <= j < |s| && s[j] == r[i];
    }
  }
}
function PySortIndexFrom(lo: int, keys: seq<seq<int>>): seq<int>
  requires 0 <= lo <= |keys|
  ensures forall i :: 0 <= i < |PySortIndexFrom(lo,keys)| ==> lo <= PySortIndexFrom(lo,keys)[i] < |keys|
  decreases |keys| - lo
{ if lo == |keys| then [] else (PyInsertIndexBounds(lo,PySortIndexFrom(lo+1,keys),keys,lo); PyInsertIndex(lo,PySortIndexFrom(lo+1,keys),keys)) }
lemma PyInsertIndexFacts(x: int, s: seq<int>, keys: seq<seq<int>>)
  requires 0 <= x < |keys|
  requires forall k :: 0 <= k < |keys| ==> |keys[k]| > 0
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < |keys|
  requires forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j] && keys[s[i]][0] <= keys[s[j]][0]
  requires x !in s
  ensures |PyInsertIndex(x,s,keys)| == |s|+1
  ensures forall v :: v in PyInsertIndex(x,s,keys) <==> v == x || v in s
  ensures forall i :: 0 <= i < |PyInsertIndex(x,s,keys)| ==> 0 <= PyInsertIndex(x,s,keys)[i] < |keys|
  ensures forall i,j :: 0 <= i < j < |PyInsertIndex(x,s,keys)| ==> PyInsertIndex(x,s,keys)[i] != PyInsertIndex(x,s,keys)[j] && keys[PyInsertIndex(x,s,keys)[i]][0] <= keys[PyInsertIndex(x,s,keys)[j]][0]
  decreases |s|
{
  if |s| > 0 {
    assert s == [s[0]]+s[1..];
    if PyLexSeq(keys[x],keys[s[0]]) {
      assert keys[x][0] <= keys[s[0]][0];
      forall j | 0 <= j < |s| ensures keys[x][0] <= keys[s[j]][0] {
        if j>0 { assert keys[s[0]][0] <= keys[s[j]][0]; }
      }
    } else {
      PyInsertIndexFacts(x,s[1..],keys);
      var tail := PyInsertIndex(x,s[1..],keys);
      forall j | 0 <= j < |tail| ensures tail[j] != s[0] && keys[s[0]][0] <= keys[tail[j]][0] {
        assert tail[j] in tail;
        if tail[j] != x {
          assert tail[j] in s[1..];
          var k :| 0 <= k < |s[1..]| && s[1..][k] == tail[j];
          assert s[k+1] != s[0];
          assert keys[s[0]][0] <= keys[s[k+1]][0];
        }
      }
    }
  }
}
lemma PySortIndexFacts(lo: int, keys: seq<seq<int>>)
  requires 0 <= lo <= |keys|
  requires forall k :: 0 <= k < |keys| ==> |keys[k]| > 0
  ensures |PySortIndexFrom(lo,keys)| == |keys|-lo
  ensures forall i :: 0 <= i < |PySortIndexFrom(lo,keys)| ==> lo <= PySortIndexFrom(lo,keys)[i] < |keys|
  ensures forall v :: v in PySortIndexFrom(lo,keys) <==> lo <= v < |keys|
  ensures forall i,j :: 0 <= i < j < |PySortIndexFrom(lo,keys)| ==> PySortIndexFrom(lo,keys)[i] != PySortIndexFrom(lo,keys)[j] && keys[PySortIndexFrom(lo,keys)[i]][0] <= keys[PySortIndexFrom(lo,keys)[j]][0]
  decreases |keys|-lo
{
  if lo < |keys| {
    PySortIndexFacts(lo+1,keys);
    var tail := PySortIndexFrom(lo+1,keys);
    assert lo !in tail;
    PyInsertIndexFacts(lo,tail,keys);
  }
}
'''

PREAMBLE += r'''
function PyBisect2(s: seq<(int,int)>, x: (int,int), lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  requires forall i,j :: 0 <= i < j < |s| ==> PyLex2(s[i],s[j])
  ensures lo <= PyBisect2(s,x,lo,hi) <= hi
  ensures forall i :: lo <= i < PyBisect2(s,x,lo,hi) ==> PyLex2(s[i],x)
  ensures forall i :: PyBisect2(s,x,lo,hi) <= i < hi ==> !PyLex2(s[i],x)
  decreases hi-lo
{
  if lo == hi then lo else
  var mid := (lo+hi)/2;
  if PyLex2(s[mid],x) then PyBisect2(s,x,mid+1,hi) else PyBisect2(s,x,lo,mid)
}
'''

PREAMBLE += r'''
lemma PySortIndexPrimary(keys: seq<seq<int>>, primary: seq<int>)
  requires |keys| == |primary|
  requires forall i :: 0 <= i < |keys| ==> |keys[i]| > 0 && keys[i][0] == primary[i]
  ensures forall i :: 0 <= i < |PySortIndexFrom(0,keys)| ==> (forall j :: i+1 <= j < |PySortIndexFrom(0,keys)| ==> PySortIndexFrom(0,keys)[i] != PySortIndexFrom(0,keys)[j] && primary[PySortIndexFrom(0,keys)[i]] <= primary[PySortIndexFrom(0,keys)[j]])
{
  PySortIndexFacts(0,keys);
  var order := PySortIndexFrom(0,keys);
  forall i | 0 <= i < |order|
    ensures forall j :: i+1 <= j < |order| ==> order[i] != order[j] && primary[order[i]] <= primary[order[j]]
  {
    forall j | i+1 <= j < |order|
      ensures order[i] != order[j] && primary[order[i]] <= primary[order[j]]
    { assert keys[order[i]][0] <= keys[order[j]][0]; }
  }
}
'''
