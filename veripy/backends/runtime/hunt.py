"""CrossHair execution and result classification for compiled contracts."""
from __future__ import annotations
import shutil
import subprocess
import sys
from pathlib import Path
from veripy.verification.runner import atomic_write_text
from veripy.frontend.extract import parse_source
from .emit import emit_checked

_REFUTATION_MARKER = "error: false when calling"

def _find_crosshair() -> str | None:
    exe = shutil.which("crosshair")
    if exe:
        return exe
    candidate = Path(sys.executable).parent / "crosshair"
    return str(candidate) if candidate.exists() else None

def _hunt(source: str, name: str, workdir: Path, per_condition_timeout: int,
          wall: int | None = None) -> tuple[str, str]:
    """Emit runtime contracts and let CrossHair hunt. Returns (verdict,
    detail) with verdict one of: 'clean', 'counterexample' (the SPEC was
    refuted), 'crash' (an uncaught exception — a real fault, but not one
    the specification discriminated), 'timeout' (the wall was exhausted —
    inconclusive), or 'error'."""
    exe = _find_crosshair()
    if exe is None:
        return "error", "crosshair not installed"
    specs = parse_source(source)
    if specs.errors or specs.orphans:
        return "error", "spec errors"
    checked = workdir / f"{name}_checked.py"
    try:
        checked.parent.mkdir(parents=True, exist_ok=True)
        atomic_write_text(checked,
                          emit_checked(source, specs, src_name=f"{name}.py"))
    except OSError as exc:
        # Unwritable workdir degrades to a per-item ERROR, same as a
        # stuck analysis — never abort the run mid-scorecard.
        return "error", f"could not stage checked module: {type(exc).__name__}"
    try:
        proc = subprocess.run(
            [exe, "check", str(checked), "--analysis_kind", "icontract",
             "--per_condition_timeout", str(per_condition_timeout)],
            capture_output=True, text=True,
            timeout=wall if wall is not None else per_condition_timeout * 40 + 120,
        )
    except subprocess.TimeoutExpired:
        # A hunt that exhausts its wall is its own verdict: for mutants a
        # diverging loop is the common cause, and divergence is a behavior
        # change (this toolchain proves termination at R4).
        return "timeout", "hunt wall exceeded (nonterminating mutant?)"
    except OSError as exc:
        # An unlaunchable analysis must degrade to a per-item ERROR,
        # never abort the surrounding verification run.
        return "error", f"crosshair failed to run: {type(exc).__name__}"
    if proc.returncode == 0:
        return "clean", ""
    if proc.returncode == 1:
        output = (proc.stdout + proc.stderr).strip()
        first = output.splitlines()[0] if output else ""
        if _REFUTATION_MARKER in output:
            return "counterexample", first
        return "crash", first
    return "error", f"crosshair exited {proc.returncode}"
