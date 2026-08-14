"""Proof-failure fixits.

Written from a feedback-sufficiency exercise: an unannotated in-fragment
function was taken to `verified` using tool output alone, and the single
place the tools ran out was an unproved postcondition over a loop — the
message named the symptom and not the remedy, and the remedy was one
`#@ invariant` line.
"""

from dataclasses import dataclass

from lemmapy.frontend.extract import parse_source
from lemmapy.hints import proof_hint

LOOP_NO_INVARIANT = (
    "#@ ensures 0 <= result <= len(xs)\n"
    "def count_evens(xs: list[int]) -> int:\n"
    "    total = 0\n"
    "    for i in range(len(xs)):\n"
    "        if xs[i] % 2 == 0:\n"
    "            total = total + 1\n"
    "    return total\n"
)

LOOP_WITH_INVARIANT = (
    "#@ ensures 0 <= result <= len(xs)\n"
    "def count_evens(xs: list[int]) -> int:\n"
    "    total = 0\n"
    "    for i in range(len(xs)):\n"
    "        #@ invariant 0 <= total <= i\n"
    "        if xs[i] % 2 == 0:\n"
    "            total = total + 1\n"
    "    return total\n"
)

TWO_LOOPS_ONE_BARE = (
    "#@ ensures 0 <= result\n"
    "def two_phase(xs: list[int]) -> int:\n"
    "    total = 0\n"
    "    for i in range(len(xs)):\n"
    "        #@ invariant 0 <= total\n"
    "        total = total + 1\n"
    "    extra = 0\n"
    "    for j in range(len(xs)):\n"
    "        extra = extra - 1\n"
    "    return total + extra\n"
)

NESTED_INVARIANT_ON_INNER_LOOP = (
    "#@ ensures 0 <= result\n"
    "def grid(n: int) -> int:\n"
    "    total = 0\n"
    "    for i in range(n):\n"
    "        for j in range(n):\n"
    "            #@ invariant 0 <= total\n"
    "            total = total + 1\n"
    "    return total\n"
)

EARLY_RETURN_BEFORE_THE_LOOP = (
    "#@ ensures 0 <= result\n"
    "def maybe(xs: list[int]) -> int:\n"
    "    if len(xs) == 0:\n"
    "        return -1\n"
    "    total = 0\n"
    "    for i in range(len(xs)):\n"
    "        total = total + 1\n"
    "    return total\n"
)

NO_LOOP = (
    "#@ ensures result == x + 1\n"
    "def bump(x: int) -> int:\n"
    "    return x + 1\n"
)


@dataclass
class FakeDiag:
    obligation: str
    py_line: int | None


def _hint(source, kind, line):
    return proof_hint(FakeDiag(kind, line), source, parse_source(source))


def test_unproved_postcondition_over_a_bare_loop_names_the_remedy():
    hint = _hint(LOOP_NO_INVARIANT, "postcondition", 7)
    assert hint and "#@ invariant" in hint and "count_evens" in hint


def test_hint_changes_once_an_invariant_exists():
    # Telling someone to add an invariant they already wrote is worse than
    # silence: it reads as the tool not having looked.
    hint = _hint(LOOP_WITH_INVARIANT, "postcondition", 8)
    assert hint and "#@ invariant" not in hint
    assert "strengthened" in hint


def test_an_invariant_on_one_loop_does_not_answer_for_another():
    # The whole-function question ("does this function have an invariant?")
    # said yes here and produced the strengthen advice, sending the reader to
    # edit the clause on the FIRST loop when the missing ingredient is a new
    # one on the second. Naming the bare loop's line is the point of the hint.
    hint = _hint(TWO_LOOPS_ONE_BARE, "postcondition", 10)
    assert hint and "#@ invariant" in hint
    assert "line 8" in hint and "strengthen" not in hint


def test_an_inner_loops_invariant_is_not_credited_to_the_outer_loop():
    # The inner invariant sits inside the outer loop's span, so containment
    # alone would mark the outer loop as covered; only innermost ownership
    # reports the outer loop as the bare one.
    hint = _hint(NESTED_INVARIANT_ON_INNER_LOOP, "postcondition", 8)
    assert hint and "line 4" in hint


def test_a_return_before_every_loop_gets_no_loop_advice():
    # This path never entered the loop, so the loop cannot be why it failed.
    assert _hint(EARLY_RETURN_BEFORE_THE_LOOP, "postcondition", 4) is None


def test_no_loop_means_no_invariant_advice():
    # A postcondition failure with no loop in sight has a different cause,
    # so guessing would send the reader down the wrong path.
    assert _hint(NO_LOOP, "postcondition", 3) is None


def test_other_kinds_get_their_own_remedy():
    assert "ENTRY" in _hint(LOOP_WITH_INVARIANT, "invariant", 5)
    assert "decreases" in _hint(LOOP_NO_INVARIANT, "termination", 4)
    assert "domain condition" in _hint(LOOP_NO_INVARIANT, "call-precondition", 5)
    assert "never attempted" in _hint(LOOP_NO_INVARIANT, "resolution", 4)


def test_unadvisable_shapes_stay_silent():
    # No line, unknown kind, or unparseable source: silence beats a guess.
    assert proof_hint(FakeDiag("postcondition", None), LOOP_NO_INVARIANT,
                      parse_source(LOOP_NO_INVARIANT)) is None
    assert _hint(LOOP_NO_INVARIANT, "bounds", 5) is None
    assert proof_hint(FakeDiag("postcondition", 2), "def f(:\n",
                      parse_source(NO_LOOP)) is None
