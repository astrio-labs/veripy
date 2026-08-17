"""The Lean 4 prelude: Python semantics, pinned.

Slice 1 needs almost nothing — `min`/`max` on `Int` and `omega` are core
Lean — so the prelude is deliberately tiny and the artifact needs NO lake
project and NO external dependencies: bare `lean --json file.lean`
elaborates against core, which kills the build-latency risk the ROADMAP
flagged for the repair loop.

Every definition here must match CPython on the shared domain, and the
match is pinned by the cross-backend differential fidelity tests (the R5
rung, extended to Lean in this track). Versioned like the Dafny preamble:
provenance rides every payload, and two "ok" verdicts must be comparable.
"""

PRELUDE_VERSION = "lean-0.1"

PRELUDE = """\
-- lemmapy Lean prelude {version} (slice 1: loop-free integer functions)
-- Python semantics on Int. Every def must match CPython on the shared
-- domain; the differential fidelity suite pins the correspondence.

def PyAbs (a : Int) : Int := if a < 0 then -a else a
""".format(version=PRELUDE_VERSION)

# Line count the prelude prepends before the first encoded definition —
# the encoder's line_map starts after it.
PRELUDE_LINES = PRELUDE.count("\n")
