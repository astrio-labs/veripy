"""The Lean backend behind the `ProofBackend` protocol (slice 1).

Loop-free integer functions, proved by a fixed core-only tactic script —
the first out-of-Dafny prover behind the seam. Sidecars are the track's
P3: a `.proofs.lean` on disk or a non-empty sidecar proposal is REFUSED
loudly (never silently ignored — a user who wrote lemmas must not
believe they were used).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from ..base import register_backend
from ..dafny.encoder import EncodeError
from .driver import lean_version, verify_lean_file
from .encoder import encode_module_lean
from .prelude import PRELUDE_VERSION


@dataclass(frozen=True)
class _EmptySidecar:
    text: str = ""
    lemmas: frozenset = frozenset()


class LeanBackend:
    name = "lean"
    preamble_version = PRELUDE_VERSION

    def prover_version(self) -> str | None:
        return lean_version()

    def sidecar_path(self, source_path: Path) -> Path:
        return source_path.with_name(source_path.stem + ".proofs.lean")

    def load_sidecar(self, source_path: Path) -> Any:
        found = self.sidecar_path(source_path)
        if found.exists():
            raise EncodeError(
                f"{found.name}: Lean proof sidecars land in the track's P3 "
                f"— refusing to verify while ignoring lemmas you wrote",
                None, rule="lean-slice-1")
        return _EmptySidecar()

    def validate_sidecar(self, text: str) -> None:
        if text.strip():
            raise EncodeError(
                "Lean proof sidecars land in the track's P3",
                None, rule="lean-slice-1")

    def encode(self, source: str, specs: Any, *, module_name: str,
               proof_lemmas: Any) -> Any:
        return encode_module_lean(source, specs, module_name=module_name,
                                  proof_lemmas=proof_lemmas)

    def encoded_text(self, encoded: Any) -> str:
        return encoded.lean_source

    def artifact_name(self, stem: str) -> str:
        return f"{stem}.lean"

    def verify_artifact(self, artifact: Path, line_map: dict[int, int], *,
                        time_limit: int, extent: int | None) -> Any:
        return verify_lean_file(artifact, line_map, time_limit=time_limit,
                                stub_extent=extent)


register_backend("lean", LeanBackend)
