// Reusable arithmetic loop predicate and a checked preservation lemma.
predicate Progress(value: int, start: int, stride: int, index: int)
{ value == start + index * stride }

lemma ProgressStep(value: int, start: int, stride: int, index: int)
  requires Progress(value, start, stride, index)
  ensures Progress(value + stride, start, stride, index + 1)
{}
