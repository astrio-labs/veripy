"""Boundary guards (ARCHITECTURE §4): generated wrappers that keep verified
guarantees when untyped Python calls in."""

from veripy.guards.emitter import GuardGenError, emit_guarded
from veripy.guards.runtime import (
    GuardError,
    PostconditionError,
    PreconditionError,
    TypeGuardError,
)

__all__ = [
    "GuardError",
    "GuardGenError",
    "PostconditionError",
    "PreconditionError",
    "TypeGuardError",
    "emit_guarded",
]
