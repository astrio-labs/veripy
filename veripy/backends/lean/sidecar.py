"""Lean proof sidecars: `<stem>.proofs.lean` beside the source.

The channel a `#@ proof` clause names. Lemma packs live here rather
than in the encoder so that what the prover is handed stays auditable:
the whitelist below decides what a pack may contain, and it is
deliberately a small allowlist of PROVED declarations rather than a
blocklist of known-bad ones.

Lean needs a stricter reading than Dafny in one place and a laxer one
in another. Stricter: `sorry` and `native_decide` both produce a
"proof" the kernel never checks, so they are banned outright. Laxer:
Lean rejects a bodiless declaration itself, so the bodiless-lemma
masquerade the Dafny validator hunts for cannot be written here.

Packs are spliced directly after the prelude, before the generated
definitions. Every pack the corpus actually uses is pure arithmetic
(divisibility, mod/pow, the Gauss step), so nothing needs to see the
encoded functions. A pack that does reference one fails with Lean's
own unknown-identifier error, which names the offending symbol.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from ..dafny.encoder import EncodeError

_RULE = "lean-sidecar"

# Tokens that would let a pack assert rather than prove. `axiom` and
# `sorry` are the direct routes; `native_decide` closes a goal by
# running compiled code the kernel never re-checks; `unsafe`/`partial`
# escape termination checking; the attribute and metaprogramming forms
# can replace a definition's meaning after the fact; `set_option` can
# turn checks off.
_FORBIDDEN = (
    "axiom", "sorry", "native_decide", "unsafe", "partial", "opaque",
    "extern", "implemented_by", "macro", "macro_rules", "syntax",
    "elab", "notation", "set_option", "#eval", "instance",
)

_DECL = re.compile(r"^\s*(theorem|lemma|def)\s+([^\s:({\[]+)", re.M)
_COMMENT_LINE = re.compile(r"--.*?$", re.M)
_COMMENT_BLOCK = re.compile(r"/-.*?-/", re.S)


def _strip_comments(text: str) -> str:
    return _COMMENT_LINE.sub("", _COMMENT_BLOCK.sub("", text))


@dataclass
class LeanSidecar:
    text: str
    lemmas: frozenset[str]
    path: Path | None = None

    @staticmethod
    def empty() -> "LeanSidecar":
        return LeanSidecar("", frozenset())


def validate_sidecar_text(text: str, name: str) -> frozenset[str]:
    """Whitelist a Lean pack and return the names it declares.

    Raises EncodeError (with `.rule` set) on rejection, so the repair
    loop can count WHICH rule fired rather than parsing prose."""
    stripped = _strip_comments(text)
    for tok in _FORBIDDEN:
        # Word-boundary match so `sorry` fires but `sorryish` does not,
        # and `#eval` (which has no word boundary at `#`) still fires.
        pattern = (re.escape(tok) if not tok[0].isalpha()
                   else rf"\b{re.escape(tok)}\b")
        if re.search(pattern, stripped):
            raise EncodeError(
                f"proof sidecar {name}: {tok!r} is not allowed — a pack "
                f"may contain only PROVED declarations, and this would "
                f"let it assert instead",
                None, rule=_RULE)
    names = frozenset(m.group(2) for m in _DECL.finditer(stripped))
    if not names:
        raise EncodeError(
            f"proof sidecar {name}: no `theorem`, `lemma`, or `def` "
            f"declaration found — an empty pack is more likely a "
            f"mistake than an intention",
            None, rule=_RULE)
    return names


def load_lean_sidecar(source_path: Path) -> LeanSidecar:
    sidecar = source_path.with_name(source_path.stem + ".proofs.lean")
    if not sidecar.exists():
        return LeanSidecar.empty()
    text = sidecar.read_text()
    lemmas = validate_sidecar_text(text, sidecar.name)
    header = f"\n-- ---- proof additions from {sidecar.name} ----\n"
    return LeanSidecar(header + text, lemmas, path=sidecar)
