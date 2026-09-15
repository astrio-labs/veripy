"""Lean backend with arithmetic and typed imperative executable models.

Proof sidecars are checked by Lean and the driver audits theorem axioms.
Unsupported Python syntax fails admission; no Dafny proof verdict is reused.
"""

from __future__ import annotations

import json
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from veripy.backends.base import register_backend
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.lean.driver import lean_version, verify_lean_file
from veripy.backends.lean.encoder import encode_module_lean
from veripy.backends.lean.prelude import PRELUDE_VERSION
from veripy.backends.lean.sidecar import load_lean_sidecar, validate_sidecar_text


@dataclass(frozen=True)
class _EmptySidecar:
    text: str = ""
    lemmas: frozenset = frozenset()


class LeanBackend:
    name = "lean"
    @property
    def preamble_version(self):
        from veripy.backends.lean.decimal import version
        return PRELUDE_VERSION + "+imperative-0.3-" + version()

    def prover_version(self) -> str | None:
        return lean_version()

    def sidecar_path(self, source_path: Path) -> Path:
        return source_path.with_name(source_path.stem + ".proofs.lean")

    def load_sidecar(self, source_path: Path) -> Any:
        return load_lean_sidecar(source_path)

    def validate_sidecar(self, text: str) -> None:
        validate_sidecar_text(text, "proofs.lean")

    def compose_artifact(self, encoded: Any, sidecar: Any) -> str:
        """Place proved support after the model for imperative programs.

Legacy arithmetic packs remain immediately after the prelude. Record/loop packs
can refer to generated definitions, never replace them. Keep diagnostic coordinates
correct across the insertion in both paths.
        """
        text = encoded.lean_source
        encoded.artifact_extent = text.count("\n") + 1
        encoded.sidecar_ranges = []
        if not sidecar.text:
            return text
        proof_marker = "-- VERIPY IMPERATIVE PROOF SUPPORT\n"
        marker = proof_marker if proof_marker in text else "end VeriPy\n"
        sections = [(marker, sidecar.text)]
        separator = "-- VERIPY PRELUDE END\n"
        if separator in sidecar.text:
            if marker != proof_marker or sidecar.text.count(separator) != 1:
                raise EncodeError("split proof preludes require an imperative model and one separator",
                                  None, rule="lean-sidecar")
            early, late = sidecar.text.split(separator)
            sections = [("-- VERIPY MODEL PRELUDE\n" if "-- VERIPY MODEL PRELUDE\n" in text else "end VeriPy\n", early), (proof_marker, late)]
        inserts = []
        for anchor, support in sections:
            at = text.find(anchor)
            cut = at + len(anchor) if at >= 0 else len(text)
            block = support + "\n"
            inserts.append((cut, text[:cut].count("\n"), block))
        inserts.sort()
        original_map = getattr(encoded, "_uncomposed_line_map", dict(encoded.line_map))
        encoded._uncomposed_line_map = original_map
        encoded.line_map = {
            line + sum(block.count("\n") for _, before, block in inserts if line > before): py
            for line, py in original_map.items()
        }
        shift = 0
        for _, before, block in inserts:
            added = block.count("\n")
            encoded.sidecar_ranges.append((before + shift + 1, before + shift + added))
            shift += added
        final = text
        for cut, _, block in reversed(inserts):
            final = final[:cut] + block + final[cut:]
        encoded.artifact_extent = final.count("\n") + 1
        return final

    def encode(self, source: str, specs: Any, *, module_name: str,
               proof_lemmas: Any) -> Any:
        try:
            return encode_module_lean(source, specs, module_name=module_name,
                                      proof_lemmas=proof_lemmas)
        except EncodeError:
            from veripy.backends.lean.imperative import encode_imperative
            return encode_imperative(source, specs, module_name, proof_lemmas)

    def encoded_text(self, encoded: Any) -> str:
        return encoded.lean_source

    def artifact_name(self, stem: str) -> str:
        return f"{stem}.lean"

    def verify_artifact(self, artifact: Path, line_map: dict[int, int], *,
                        time_limit: int, extent: int | None) -> Any:
        started = time.monotonic()
        result = verify_lean_file(artifact, line_map, time_limit=time_limit,
                                  stub_extent=extent)
        # Same-content concurrent calls may have different budgets/outcomes.
        # Keep each invocation's evidence separate instead of overwriting it.
        invocation = uuid.uuid4().hex
        log = artifact.with_name(f"{artifact.stem}.{invocation}.lean.log")
        audit = artifact.with_name(f"{artifact.stem}.{invocation}.lean.audit.json")
        result.log_path, result.audit_path = str(log), str(audit)
        log.write_text(result.raw)
        audit.write_text(json.dumps({
            "ok": result.ok, "error": result.error, "summary": result.summary,
            "wall_limit_seconds": time_limit,
            "elapsed_seconds": time.monotonic() - started,
            "axiom_messages": [d.message for d in result.diagnostics
                               if "axioms" in d.message or "axiom audit" in d.message],
            "errors": [d.message for d in result.diagnostics if d.severity == "error"],
        }, indent=2) + "\n")
        return result


register_backend("lean", LeanBackend)
