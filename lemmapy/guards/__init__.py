"""Boundary guards (ARCHITECTURE §4): generated wrappers that keep verified
guarantees when untyped Python calls in."""

from .emitter import GuardGenError, emit_guarded
from .runtime import (
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
