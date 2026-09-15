import re
from typing import NewType, cast
NormalizedName = NewType("NormalizedName", str)
class InvalidName(ValueError):
    """
    An invalid distribution name; users should refer to the packaging user guide.
    """
_validate_regex = re.compile(r"[A-Z0-9]|[A-Z0-9][A-Z0-9._-]*[A-Z0-9]", re.IGNORECASE)
_normalized_regex = re.compile(r"[a-z0-9]|[a-z0-9]([a-z0-9-](?!--))*[a-z0-9]")

#@ ghost_ensures ghost("VPackagingOutcome", name, validate, result, raised())
#@ ensures raised() or "--" not in result
def canonicalize_name(name: str, *, validate: bool = False) -> NormalizedName:
    if validate and not _validate_regex.fullmatch(name):
        raise InvalidName(f"name is invalid: {name!r}")
    # Ensure all ``.`` and ``_`` are ``-``
    # Emulates ``re.sub(r"[-_.]+", "-", name).lower()`` from PEP 503
    # Much faster than re, and even faster than str.translate
    value = name.lower().replace("_", "-").replace(".", "-")
    # Condense repeats (faster than regex)
    while "--" in value:
        #@ invariant ghost("VPackagingInvariant", name, value)
        #@ decreases len(value)
        #@ proof VPackagingReplace(value)
        value = value.replace("--", "-")
    #@ proof VPackagingFinished(value)
    return cast("NormalizedName", value)

#@ ghost_ensures ghost("VPackagingNormalized", name, result, raised())
def is_normalized_name(name: str) -> bool:
    return _normalized_regex.fullmatch(name) is not None
