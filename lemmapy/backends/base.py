"""The proof-backend protocol: the seam a second prover plugs into.

Everything above this line — the `#@` spec surface, the failure taxonomy,
the exams, the mutant panels, the staging/atomic-write machinery in
`agentio` — is backend-neutral. Everything below it is one prover's
business: how a module encodes, what the sidecar file is called, how the
prover is invoked, and what its diagnostics look like. This module names
that seam so a Lean backend is an implementation, not a rewrite
(ROADMAP: "Lean backend — active pre-workshop track").

Shape notes, deliberately conservative for P0:

- The protocol mirrors the Dafny backend's existing call shapes exactly.
  `encoded.line_map`, sidecar `.lemmas`/`.text`, and verify-result
  `.ok`/`.error`/`.diagnostics` are already neutral; the one
  Dafny-flavored attribute (`dafny_source`) hides behind
  `encoded_text()`. Neutralizing the payload schema's `dafny_line` field
  is a versioned AGENT-INTERFACE change and is NOT this seam's job.
- Registration is lazy: `get_backend` imports a backend's module on first
  use, so importing `lemmapy` never pays for provers that are not
  installed.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Callable, Protocol, runtime_checkable


@runtime_checkable
class ProofBackend(Protocol):
    """What a prover backend must provide. See `backends/dafny/backend.py`
    for the reference implementation and the semantics of each member."""

    name: str
    preamble_version: str

    def prover_version(self) -> str | None: ...

    def sidecar_path(self, source_path: Path) -> Path: ...

    def load_sidecar(self, source_path: Path) -> Any: ...

    def validate_sidecar(self, text: str) -> None: ...

    def encode(self, source: str, specs: Any, *, module_name: str,
               proof_lemmas: Any) -> Any: ...

    def encoded_text(self, encoded: Any) -> str: ...

    def artifact_name(self, stem: str) -> str: ...

    def verify_artifact(self, artifact: Path, line_map: dict[int, int], *,
                        time_limit: int,
                        extent: int | None) -> Any: ...


# name -> zero-arg factory. Factories run once; the instance is cached.
_FACTORIES: dict[str, Callable[[], ProofBackend]] = {}
_INSTANCES: dict[str, ProofBackend] = {}

# Backends whose modules register on import, keyed by the name callers use.
# Lazy so `import lemmapy` never imports a prover integration it does not
# need (and so a future lean backend can require lake/lean only when asked
# for).
_LAZY_MODULES: dict[str, str] = {
    "dafny": "lemmapy.backends.dafny.backend",
}


def register_backend(name: str, factory: Callable[[], ProofBackend]) -> None:
    _FACTORIES[name] = factory


def available_backends() -> list[str]:
    """Names `get_backend` accepts, registered or lazily registrable."""
    return sorted(set(_FACTORIES) | set(_LAZY_MODULES))


def get_backend(name: str = "dafny") -> ProofBackend:
    """The backend instance for `name` (a cached singleton per name).

    Unknown names fail loudly with the known set — a typo must never
    silently fall back to another prover, for exactly the reason the
    engine layer refuses silent model substitution: the backend name is
    provenance, and every payload built under it is labelled by it.
    """
    if name in _INSTANCES:
        return _INSTANCES[name]
    if name not in _FACTORIES and name in _LAZY_MODULES:
        import importlib

        importlib.import_module(_LAZY_MODULES[name])
    if name not in _FACTORIES:
        raise ValueError(
            f"unknown backend {name!r} (available: "
            f"{', '.join(available_backends())})")
    _INSTANCES[name] = _FACTORIES[name]()
    return _INSTANCES[name]
