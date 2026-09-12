"""Immutable materialized tuples remain distinct from mutable Python lists."""
PREAMBLE = '''
datatype VChecksumTuple<T> = VChecksumTupleMake(VChecksumValues: seq<T>)
function VChecksumReverse<T>(s: seq<T>): seq<T> {
  seq(|s|, i requires 0 <= i < |s| => s[|s|-1-i])
}
function VChecksumStep<T>(s: seq<T>, step: int): seq<T>
  requires step > 0
  decreases |s|
{ if |s| == 0 then [] else [s[0]] + VChecksumStep(s[PyMin(step,|s|)..],step) }
function VChecksumStride<T>(s: seq<T>, lo: int, hi: int, step: int): seq<T>
  requires step > 0
{ VChecksumStep(PySlice(s,lo,hi),step) }
function VChecksumIndex(s: string, needle: string): int
  requires PyStrFind(s,needle) >= 0
{ PyStrFind(s,needle) }
'''


def element(dtype):
    return dtype[len('VChecksumTuple<'):-1] if dtype and dtype.startswith('VChecksumTuple<') else None
