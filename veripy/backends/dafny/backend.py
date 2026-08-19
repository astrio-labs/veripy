"""The Dafny backend behind the `ProofBackend` protocol.

Pure delegation — every operation is the pre-protocol function it names,
so behavior is pinned by the existing suite. The value is the seam: the
consumer surface that used to be six direct imports across three modules
(plus `validate_sidecar_text` in the repair loop) is now one object a
`--backend` flag can swap.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from ..base import register_backend
from .driver import dafny_version, verify_dafny_file
from .encoder import encode_module, load_proof_sidecar, validate_sidecar_text
from .preamble import PREAMBLE_VERSION


class DafnyBackend:
    name = "dafny"
    preamble_version = PREAMBLE_VERSION

    def prover_version(self) -> str | None:
        return dafny_version()

    def sidecar_path(self, source_path: Path) -> Path:
        return source_path.with_name(source_path.stem + ".proofs.dfy")

    def load_sidecar(self, source_path: Path) -> Any:
        return load_proof_sidecar(source_path)

    def validate_sidecar(self, text: str) -> None:
        validate_sidecar_text(text)

    def encode(self, source: str, specs: Any, *, module_name: str,
               proof_lemmas: Any) -> Any:
        return encode_module(source, specs, module_name=module_name,
                             proof_lemmas=proof_lemmas)

    def encoded_text(self, encoded: Any) -> str:
        return encoded.dafny_source

    def artifact_name(self, stem: str) -> str:
        return f"{stem}.dfy"

    def verify_artifact(self, artifact: Path, line_map: dict[int, int], *,
                        time_limit: int, extent: int | None) -> Any:
        return verify_dafny_file(artifact, line_map, time_limit=time_limit,
                                 stub_extent=extent)


register_backend("dafny", DafnyBackend)
