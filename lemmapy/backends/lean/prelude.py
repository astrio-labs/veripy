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

PRELUDE_VERSION = "lean-0.3"

# The prelude lives in its own namespace and every call site references
# it QUALIFIED (LemmaPy.PyAbs). Escaping user identifiers handles
# keywords, but «PyAbs» IS the identifier PyAbs (guillemets quote, they
# do not namespace — measured: a module `def PyAbs` failed with
# "`PyAbs` has already been declared"), so separation from user names
# has to come from the namespace: a top-level user def cannot redeclare
# a namespaced name, and a binder cannot capture a qualified reference.
#
# PySum models Python's `sum` on `list[int]` (Python folds left, PySum
# folds right; Int addition is commutative and associative, so the
# values agree). PySum_take_succ is the lemma pack behind sum-loop
# invariants: it peels the (n+1)-prefix sum into the n-prefix sum plus
# the element, which is the invariant-preservation step. It is PROVED
# here, not assumed — the prelude carries no axioms, and P3's
# `#print axioms` checker will pin that.
PRELUDE = """\
-- lemmapy Lean prelude {version} (loop-free + for-range loops + lists)
-- Python semantics on Int. Every def must match CPython on the shared
-- domain; the differential fidelity suite pins the correspondence.

namespace LemmaPy

def PyAbs (a : Int) : Int := if a < 0 then -a else a

def PySum : List Int → Int
  | [] => 0
  | x :: rest => x + PySum rest

theorem PySum_take_succ (xs : List Int) (n : Nat) :
    PySum (xs.take (n + 1)) = PySum (xs.take n) + xs.getD n 0 := by
  induction xs generalizing n with
  | nil => simp [PySum, List.getD]
  | cons a rest ih =>
    cases n with
    | zero => simp [PySum, List.getD]
    | succ m =>
      simp only [List.take_succ_cons, PySum, List.getD_cons_succ, ih m]
      omega

end LemmaPy
""".format(version=PRELUDE_VERSION)

# Line count the prelude prepends before the first encoded definition —
# the encoder's line_map starts after it.
PRELUDE_LINES = PRELUDE.count("\n")
