"""The versioned Dafny preamble (ARCHITECTURE §7.1) — Python-exact arithmetic.

Inlined into every emitted stub so stubs are self-contained. `PyMod`/
`PyFloorDiv` implement Python's floor-based semantics on top of Dafny's
Euclidean operators; they coincide exactly when the divisor is positive.

The divisibility lemma pack (needed for e.g. gcd's maximality ensures, which
times out without it) is designated future preamble work — see ROADMAP.
"""

PREAMBLE_VERSION = "0.1"

PREAMBLE = """\
// LemmaPy Dafny preamble v0.1 -- Python-exact arithmetic (ARCHITECTURE §7.1).
// PyMod/PyFloorDiv: Python floor-based // and % on Dafny's Euclidean ops.
function PyMod(a: int, b: int): int
  requires b != 0
{
  if b < 0 && a % b != 0 then a % b + b else a % b
}

function PyFloorDiv(a: int, b: int): int
  requires b != 0
{
  (a - PyMod(a, b)) / b
}

function PyMin(a: int, b: int): int { if a <= b then a else b }
function PyMax(a: int, b: int): int { if a >= b then a else b }
function PyAbs(a: int): int { if a >= 0 then a else -a }
"""
