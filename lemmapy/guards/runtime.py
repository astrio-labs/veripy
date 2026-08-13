"""Runtime support imported by generated guard modules (ARCHITECTURE §4).

The verified guarantee only covers executions whose inputs satisfy the
proof's assumptions. Guards make that boundary checkable:

- **Deep exact-type checks** — `type(x) is int` exactness, elementwise on
  lists, so `json.loads` booleans/floats, `typing.cast` lies, and list
  subclasses with overridden methods are all rejected at the boundary.
  (`bool` is a subclass of `int` in Python, but the proof modeled `int`;
  exactness keeps the model honest.)
- **Copy-in** — list arguments are copied to fresh `list` objects at every
  depth, so caller-held aliases can neither violate the ownership
  discipline nor mutate values mid-call.
- **Blame** — every guard failure names the function, the offending value
  path, and who is at fault: the caller (bad input) or the
  callee/toolchain (a proven property failed at runtime).

Type descriptors are nested tuples mirroring the fragment's annotation
grammar: ("int",), ("bool",), ("str",), ("list", inner), ("opt", inner).
"""

from __future__ import annotations

Descriptor = tuple


class GuardError(Exception):
    """Base for boundary-guard failures."""

    blame = "caller"

    def __init__(self, function: str, message: str):
        super().__init__(f"{function}: {message} [blame: {self.blame}]")
        self.function = function


class TypeGuardError(GuardError):
    """An argument failed the deep exact-type check."""

    blame = "caller"


class PreconditionError(GuardError):
    """An executable `#@ requires` clause evaluated false."""

    blame = "caller"


class PostconditionError(GuardError):
    """A proven `#@ ensures` clause evaluated false at runtime — the input
    passed every guard, so the fault is in the callee or the toolchain
    (encoder, prover, or a violated island assumption), never the caller."""

    blame = "callee-or-toolchain"


def describe(desc: Descriptor) -> str:
    kind = desc[0]
    if kind == "list":
        return f"list[{describe(desc[1])}]"
    if kind == "opt":
        return f"{describe(desc[1])} | None"
    return kind


def check_value(value: object, desc: Descriptor, *, function: str, path: str) -> None:
    """Deep exact-type check; raises TypeGuardError naming the value path."""
    kind = desc[0]
    if kind == "opt":
        if value is None:
            return
        check_value(value, desc[1], function=function, path=path)
        return
    if kind == "list":
        if type(value) is not list:
            raise TypeGuardError(
                function,
                f"{path}: expected {describe(desc)}, got {type(value).__name__}",
            )
        for i, element in enumerate(value):
            check_value(element, desc[1], function=function, path=f"{path}[{i}]")
        return
    expected = {"int": int, "bool": bool, "str": str}[kind]
    if type(value) is not expected:
        raise TypeGuardError(
            function,
            f"{path}: expected {kind}, got {type(value).__name__}",
        )
    if kind == "str":
        # Dafny's char domain is Unicode scalar values; a lone surrogate
        # has no model, so it is rejected at the boundary (ARCHITECTURE §7).
        for i, ch in enumerate(value):  # type: ignore[arg-type]
            if 0xD800 <= ord(ch) <= 0xDFFF:
                raise TypeGuardError(
                    function,
                    f"{path}[{i}]: lone surrogate U+{ord(ch):04X} is outside "
                    f"the modeled char domain",
                )


def copy_value(value: object, desc: Descriptor) -> object:
    """Descriptor-driven copy-in: fresh list objects at every depth;
    immutable leaves pass through."""
    kind = desc[0]
    if kind == "list":
        return [copy_value(e, desc[1]) for e in value]  # type: ignore[union-attr]
    if kind == "opt" and value is not None:
        return copy_value(value, desc[1])
    return value


def guard_value(value: object, desc: Descriptor, *, function: str, param: str) -> object:
    """Check then copy — the argument the island actually receives."""
    check_value(value, desc, function=function, path=param)
    return copy_value(value, desc)


class IslandIntegrityError(GuardError):
    """The on-disk island region no longer matches the embedded digest."""

    blame = "environment"


_ISLAND_BEGIN = "# ---- LEMMAPY ISLAND BEGIN (verbatim copy of the admitted source) ----\n"
_ISLAND_END = "\n# ---- LEMMAPY ISLAND END ----"


def verify_island_integrity(guarded_path) -> str:
    """Recompute the island digest of a guarded module on disk and compare
    it with the embedded `_LEMMAPY_ISLAND_SHA256`. Returns the digest, or
    raises IslandIntegrityError on tampering (assumption A1's on-disk half
    made checkable)."""
    import re
    from pathlib import Path

    text = Path(guarded_path).read_text()
    # Exactly one of each sentinel: injected duplicates would let a
    # crafted file truncate the digest's coverage while the real island
    # region carries unhashed code.
    if text.count(_ISLAND_BEGIN) != 1 or text.count(_ISLAND_END) != 1:
        raise IslandIntegrityError(
            str(guarded_path), "island sentinels missing or duplicated")
    island = text.split(_ISLAND_BEGIN, 1)[1].split(_ISLAND_END, 1)[0]
    m = re.search(r'^_LEMMAPY_ISLAND_SHA256 = "([0-9a-f]{64})"$', text, re.M)
    if m is None:
        raise IslandIntegrityError(str(guarded_path), "embedded digest missing")
    import hashlib

    actual = hashlib.sha256(island.encode()).hexdigest()
    if actual != m.group(1):
        raise IslandIntegrityError(
            str(guarded_path),
            f"island digest mismatch: embedded {m.group(1)[:12]}…, "
            f"on disk {actual[:12]}…",
        )
    return actual
