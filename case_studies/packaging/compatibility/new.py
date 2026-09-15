from __future__ import annotations
import re
from typing import NewType, cast
NormalizedName = NewType('NormalizedName', str)

class InvalidName(ValueError):
    """
    An invalid distribution name; users should refer to the packaging user guide.
    """
_validate_regex = re.compile('[A-Z0-9]|[A-Z0-9][A-Z0-9._-]*[A-Z0-9]', re.IGNORECASE)

def canonicalize_name(name: str, *, validate: bool=False) -> NormalizedName:
    if validate and (not _validate_regex.fullmatch(name)):
        raise InvalidName(f'name is invalid: {name!r}')
    value = name.lower().replace('_', '-').replace('.', '-')
    while '--' in value:
        value = value.replace('--', '-')
    return cast('NormalizedName', value)
