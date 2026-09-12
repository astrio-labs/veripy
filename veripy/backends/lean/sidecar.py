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

Legacy packs follow the prelude. Imperative packs follow generated model and
contract definitions. An explicit `-- VERIPY PRELUDE END` separator places
mathematical definitions before the model and their remaining lemmas after it;
both sections are checked and diagnostic positions account for both insertions.

An imperative pack can provide a theorem named `<function>__proof` with the
same arguments, preconditions and Hoare triple as the generated theorem. This
supports manually directed proofs of larger programs. The generated theorem
applies that theorem at its exact expected type; the normal kernel and axiom
checks still apply. A theorem of a weaker or unrelated type is rejected.
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
    "axiom", "sorry", "admit", "native_decide", "unsafe", "partial",
    "opaque", "extern", "implemented_by", "macro", "macro_rules",
    "syntax", "elab", "notation", "set_option", "#eval", "instance",
    "run_tac", "run_elab", "initialize", "builtin_initialize",
)
# `admit` is `sorry` wearing a tactic's clothes, and its absence here
# was a real hole. The lesson is the list's, not the entry's: a
# blocklist cannot enumerate every route to unchecked evidence. The
# axiom-footprint check in the driver is the structural answer — it
# catches `sorry` and `admit` alike, by their shared `sorryAx`, along
# with routes nobody has thought of yet. This list stays as the cheap
# first gate that refuses before Lean is ever invoked.

_DECL = re.compile(r"^\s*(theorem|lemma|def|abbrev)\s+([^\s:({\[]+)", re.M)
_COMMENT_LINE = re.compile(r"--.*?$", re.M)
_COMMENT_BLOCK = re.compile(r"/-.*?-/", re.S)


def _strip_comments(text: str) -> str:
    # Lean block comments nest, and comment delimiters in strings are data.
    # Regex removal can conceal executable commands between two string literals.
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            result.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                result.append(text[i + 1])
                i += 2
                continue
            if text[i] == '"':
                quoted = False
            i += 1
        elif text[i] == "«":
            end = text.find("»", i + 1)
            end = len(text) if end < 0 else end + 1
            result.extend(text[i:end])
            i = end
        elif text[i] == "'" and (char := re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'", text[i:])):
            result.extend(char.group())
            i += len(char.group())
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                result.extend(" " * (len(text) - i))
                break
            result.extend(" " * (end - i))
            i = end
        elif text.startswith("/-", i):
            depth = 1
            result.extend("  ")
            i += 2
        else:
            quoted = text[i] == '"'
            result.append(text[i])
            i += 1
    return "".join(result)


class LeanProofSymbols(frozenset):
    """All declared names for admission, with theorem hints tracked separately."""
    def __new__(cls, names=(), theorems=()):
        value = super().__new__(cls, names)
        value.theorems = frozenset(theorems)
        return value


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
    # Ambient commands can alter the type of subsequent generated theorems.
    # In particular `variable (h : False); include h` adds an unrequested
    # hypothesis without adding a disallowed axiom. Packs must be closed.
    ambient = re.search(r"(?<![«\w])(namespace|section|variable|variables|include|omit|open|end|attribute|export|universe|universes)(?![\w»])", stripped)
    if ambient:
        raise EncodeError(f"proof sidecar {name}: ambient command {ambient.group(1)!r} is not allowed",
                          None, rule=_RULE)
    for attribute in re.finditer(r"@\[([^]]*)\]", stripped):
        # Numeric priorities choose between already proved specifications; they
        # cannot change a declaration's meaning or disable kernel checks.
        if any(tag.strip() not in {"spec", "simp", "grind"}
               and re.fullmatch(r"spec\s+[1-9][0-9]{0,5}", tag.strip()) is None
               for tag in attribute.group(1).split(",")):
            raise EncodeError(f"proof sidecar {name}: only spec/simp/grind attributes are allowed (spec priority: 1..999999)",
                              None, rule=_RULE)
    for command in re.finditer(r"#[A-Za-z_][A-Za-z_0-9]*", stripped):
        if not re.match(r"#print\s+axioms\b", stripped[command.start():]):
            raise EncodeError(f"proof sidecar {name}: only #print axioms commands are allowed",
                              None, rule=_RULE)
    declarations = list(_DECL.finditer(stripped))
    names = LeanProofSymbols((m.group(2) for m in declarations),
                             (m.group(2) for m in declarations if m.group(1) in ("theorem", "lemma")))
    if not names:
        raise EncodeError(
            f"proof sidecar {name}: no `theorem`, `lemma`, or `def` "
            f"declaration found — an empty pack is more likely a "
            f"mistake than an intention",
            None, rule=_RULE)
    # Hint selection is only a proof-search optimization. Every declaration and
    # generated theorem is still independently checked and axiom-audited.
    names.scopes = {}
    for i, declaration in enumerate(declarations):
        end = declarations[i+1].start() if i+1 < len(declarations) else len(stripped)
        block = stripped[declaration.end():end]
        names.scopes[declaration.group(2)] = frozenset(re.findall(r"([A-Za-z_][A-Za-z_0-9]*)__+(?:inv_[0-9]+|post|error)\b", block))
    return names


# Only packaged, reviewed libraries can be requested. No filesystem imports or
# arbitrary paths are accepted. Expansion leaves artifacts fully standalone.
LIBRARIES = frozenset({"arithmetic", "allocation", "ranges"})


def expand_libraries(text: str) -> str:
    requested = re.findall(r"^-- VERIPY LIBRARY (\S+)\s*$", text, re.M)
    if len(requested) != len(set(requested)):
        raise EncodeError("duplicate Lean proof library", None, rule=_RULE)
    pieces = []
    for name in requested:
        if name not in LIBRARIES:
            raise EncodeError(f"unknown Lean proof library: {name}", None, rule=_RULE)
        content = (Path(__file__).parent / "library" / (name + ".lean")).read_text()
        validate_sidecar_text(content, name + ".lean")
        pieces.append(content)
    return "\n".join(pieces + [text])


def load_lean_sidecar(source_path: Path) -> LeanSidecar:
    sidecar = source_path.with_name(source_path.stem + ".proofs.lean")
    if not sidecar.exists():
        return LeanSidecar.empty()
    text = expand_libraries(sidecar.read_text())
    lemmas = validate_sidecar_text(text, sidecar.name)
    header = f"\n-- ---- proof additions from {sidecar.name} ----\n"
    return LeanSidecar(header + text, lemmas, path=sidecar)
