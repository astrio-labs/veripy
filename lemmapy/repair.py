"""The proof-repair loop (M2): proofs that finish themselves.

`repair_file` drives an engine (an LLM, or a scripted stand-in for tests)
against the structured-failure interface: verify → feed the failures, the
source, and the current sidecar to the engine → the engine proposes a new
`.proofs.dfy` → the whitelist validator and the prover judge it → iterate.

The engine may edit ONLY the proof sidecar. Everything else — source,
specs, the stub — is frozen; an engine cannot weaken what it is asked to
prove. Proposals run through the same `_validate_sidecar` whitelist as
hand-written sidecars (ghost lemmas with bodies only), so a repair can
never smuggle an axiom, and a rejected proposal comes back to the engine
as the next iteration's failure payload.

All work happens on copies under the workdir; the user's sidecar is only
written (with a `.bak` of any previous content) on success with
``apply=True``.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Protocol

from .agentio import verify_structured
from .backends.dafny.encoder import EncodeError, validate_sidecar_text

Engine = Callable[[dict[str, Any]], str]

RULES = """\
You are repairing a Dafny proof for a verified-Python toolchain.
You may change ONLY the proof sidecar (<stem>.proofs.dfy). Reply with the
COMPLETE new sidecar content and nothing else (no fences, no commentary).
Sidecar rules (whitelist-validated; violations are rejected):
- ghost declarations only: `lemma` / `ghost function` / `function`, each
  with a BODY (a bodiless lemma is an axiom and is rejected)
- forbidden: method, import, include, assume, axioms, attributes ({:...}),
  multiset/set/iset/map/imap, lambda arrows (=>), string @-literals
- `==>` (implication) is legal; `=>` (lambda) is not
- lemmas are invoked from Python via `#@ proof LemmaName(args)` clauses
  already present in the source; define exactly the lemmas those clauses
  name (plus any helper lemmas they call)
The preamble (PyMod, PyFloorDiv, PySlice, PySum, ...) is in scope."""


def build_request(source: str, payload: dict[str, Any],
                  attempt: int, history: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": "lemmapy-repair-request/1",
        "rules": RULES,
        "attempt": attempt,
        "source": source,
        "failures": payload,
        "sidecar": (payload.get("sidecar") or {}).get("text", ""),
        "history": history,
    }


def _render_prompt(request: dict[str, Any]) -> str:
    parts = [
        request["rules"],
        "\n## Python source (frozen)\n" + request["source"],
        "\n## Verification outcome (structured)\n"
        + json.dumps(request["failures"], indent=1),
        "\n## Current sidecar\n" + (request["sidecar"] or "(none)"),
    ]
    if request["history"]:
        parts.append("\n## Prior attempts (most recent last)\n"
                     + json.dumps(request["history"][-3:], indent=1))
    parts.append("\nReply with the complete new sidecar content only.")
    return "\n".join(parts)


def _strip_fences(text: str) -> str:
    stripped = text.strip()
    if stripped.startswith("```"):
        lines = stripped.splitlines()
        if lines[-1].strip() == "```":
            lines = lines[1:-1]
        else:
            lines = lines[1:]
        stripped = "\n".join(lines)
    return stripped.rstrip() + "\n"


def _claude_cmd(exe: str, prompt: str, model: str | None = None,
                json_output: bool = False) -> list[str]:
    """Measurement integrity: the engine must work from the request alone.
    With tools enabled, a headless agent FOUND the golden sidecar in the
    repository and returned it verbatim — a retrieval result masquerading
    as proof completion. All tools are denied, and ORDER MATTERS: the
    prompt must precede --disallowedTools (a variadic flag that would
    otherwise swallow the prompt text as tool-name rules), so
    `--disallowedTools "*"` are pinned as the FINAL two argv entries.
    Both the "*" pattern and the ordering are verified by live token-file
    probes."""
    cmd = [exe, "-p", prompt]
    if model is not None:
        cmd += ["--model", model]
    if json_output:
        cmd += ["--output-format", "json"]
    cmd += ["--disallowedTools", "*"]
    return cmd


def _parse_claude_json(stdout: str) -> tuple[str, dict[str, Any] | None]:
    """Parse `claude -p --output-format json` output into (text, usage).
    Tolerant by design: a CLI format drift degrades to text mode (usage
    None) instead of breaking runs. Field names pinned from a live 2.1.193
    sample; `models` records the RESOLVED model ids (what actually served
    the call) for the run ledger."""
    try:
        obj = json.loads(stdout)
    except (json.JSONDecodeError, ValueError):
        return stdout, None
    if not isinstance(obj, dict):
        return stdout, None
    text = obj.get("result", "")
    if obj.get("is_error"):
        raise RuntimeError(f"claude engine error: {str(text)[:400]}")
    raw = obj.get("usage") or {}
    usage = {
        "input_tokens": raw.get("input_tokens"),
        "cache_creation_input_tokens": raw.get("cache_creation_input_tokens"),
        "cache_read_input_tokens": raw.get("cache_read_input_tokens"),
        "output_tokens": raw.get("output_tokens"),
        "cost_usd": obj.get("total_cost_usd"),
        "duration_api_ms": obj.get("duration_api_ms"),
        "num_turns": obj.get("num_turns"),
        "models": sorted((obj.get("modelUsage") or {}).keys()),
    }
    return text, usage


class _ClaudeEngine:
    """Headless `claude -p` engine: no tools, and an isolated empty working
    directory (defense in depth against path guessing from the payload).
    Usage flows out via `usage_log` (one entry per call, None when the CLI
    output was not parseable JSON) — a side channel that keeps the
    `Engine = Callable[[dict], str]` contract intact."""

    def __init__(self, model: str | None = None):
        self.model = model
        self.usage_log: list[dict[str, Any] | None] = []

    def __call__(self, request: dict[str, Any]) -> str:
        exe = shutil.which("claude")
        if exe is None:
            raise RuntimeError("engine 'claude' needs the claude CLI on PATH")
        with tempfile.TemporaryDirectory(prefix="lemmapy-engine-") as sandbox:
            proc = subprocess.run(
                _claude_cmd(exe, _render_prompt(request), model=self.model,
                            json_output=True),
                capture_output=True, text=True, timeout=600, cwd=sandbox,
            )
        if proc.returncode != 0:
            raise RuntimeError(f"claude engine failed: {proc.stderr[:400]}")
        text, usage = _parse_claude_json(proc.stdout)
        self.usage_log.append(usage)
        return _strip_fences(text)


def claude_engine(request: dict[str, Any]) -> str:
    """Compatibility shim over `_ClaudeEngine` (docs and tests reference
    the function form; per-call usage is discarded here)."""
    return _ClaudeEngine()(request)


# provider -> (default base URL, API-key env var). Overridable via
# LEMMAPY_API_BASE_<PROVIDER>. `openrouter` reaches the open models
# (Kimi, GLM, ...) through one key.
_API_PROVIDERS = {
    "openai": ("https://api.openai.com/v1", "OPENAI_API_KEY"),
    "openrouter": ("https://openrouter.ai/api/v1", "OPENROUTER_API_KEY"),
}


class _ApiEngine:
    """OpenAI-compatible chat-completions engine (`api:<provider>/<model>`).
    A raw HTTP completion has no tools by construction — a strictly
    tighter sandbox than the CLI path (nothing to deny). stdlib-only on
    purpose: no new dependency for the harness."""

    def __init__(self, provider: str, model: str):
        import os

        if provider not in _API_PROVIDERS:
            known = ", ".join(sorted(_API_PROVIDERS))
            raise ValueError(f"unknown api provider {provider!r} (known: {known})")
        default_base, key_env = _API_PROVIDERS[provider]
        self.base = os.environ.get(f"LEMMAPY_API_BASE_{provider.upper()}",
                                   default_base).rstrip("/")
        self.key_env = key_env
        self.provider = provider
        self.model = model
        self.usage_log: list[dict[str, Any] | None] = []

    def __call__(self, request: dict[str, Any]) -> str:
        import os
        import urllib.request

        key = os.environ.get(self.key_env)
        if not key:
            raise RuntimeError(
                f"engine 'api:{self.provider}/{self.model}' needs "
                f"{self.key_env} set")
        body = json.dumps({
            "model": self.model,
            "messages": [{"role": "user",
                          "content": _render_prompt(request)}],
        }).encode()
        req = urllib.request.Request(
            f"{self.base}/chat/completions", data=body,
            headers={"Authorization": f"Bearer {key}",
                     "Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=600) as resp:
            obj = json.loads(resp.read().decode())
        choices = obj.get("choices") or []
        if not choices:
            raise RuntimeError(
                f"api engine returned no choices: {str(obj)[:400]}")
        raw = obj.get("usage") or {}
        self.usage_log.append({
            "input_tokens": raw.get("prompt_tokens"),
            "output_tokens": raw.get("completion_tokens"),
            "cost_usd": None,  # not reported by chat-completions APIs
            "models": [obj.get("model") or self.model],
        })
        return _strip_fences(
            (choices[0].get("message") or {}).get("content") or "")


class _FileEngine:
    """Scripted engine: returns `1.dfy`, `2.dfy`, ... from a directory in
    attempt order. Deterministic loop testing and replay of recorded runs."""

    def __init__(self, directory: Path):
        self.directory = directory
        self.calls = 0

    def __call__(self, request: dict[str, Any]) -> str:
        self.calls += 1
        candidate = self.directory / f"{self.calls}.dfy"
        if not candidate.exists():
            raise RuntimeError(f"file engine exhausted at attempt {self.calls}")
        return candidate.read_text()


def make_engine(spec: str) -> Engine:
    if spec == "claude":
        return _ClaudeEngine()
    if spec.startswith("claude:"):
        model = spec[len("claude:"):]
        # argv hygiene: an empty or dash-leading "model" would be read as a
        # flag by the CLI, silently reshaping the pinned command.
        if not model or model.startswith("-"):
            raise ValueError(f"unknown engine {spec!r}: bad model {model!r}")
        return _ClaudeEngine(model)
    if spec.startswith("api:"):
        rest = spec[len("api:"):]
        provider, sep, model = rest.partition("/")
        if not sep or not provider or not model:
            raise ValueError(
                f"unknown engine {spec!r} (use 'api:<provider>/<model>')")
        return _ApiEngine(provider, model)
    if spec.startswith("file:"):
        return _FileEngine(Path(spec[5:]))
    raise ValueError(f"unknown engine {spec!r} (use 'claude', "
                     f"'claude:<model>', 'api:<provider>/<model>', or "
                     f"'file:<dir>')")


def _acquire_apply_lock(lock: Path):
    """Advisory flock on a persistent lock file. The kernel releases the
    lock when the holder dies, so an orphaned lock cannot block applies
    (no stale-lock reaping, hence no reap races either); the empty .lock
    file itself is inert and left in place. Returns an fd to hold, or
    None on live contention."""
    import fcntl
    import os

    fd = os.open(lock, os.O_CREAT | os.O_WRONLY)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return fd
    except OSError:
        os.close(fd)
        return None


def _apply_sidecar(user_sidecar: Path, text: str, expected_prior: str | None,
                   source_path: Path, expected_source: str) -> str:
    """Write the verified sidecar beside the source: flock-serialized,
    atomic, first-backup-wins (the earliest `.bak` is the content closest
    to the user's original), first-APPLY-wins (a concurrently applied
    proof is never overwritten), and source-guarded — the live source is
    re-checked under the lock at the last instant before the write. (An
    editor saving in the microseconds after that check is inherently
    unpreventable without cooperative source locking; the window here is
    the minimum any file-writing tool can have.)"""
    import os
    import tempfile

    lock = user_sidecar.with_name(user_sidecar.name + ".lock")
    fd = _acquire_apply_lock(lock)
    if fd is None:
        return ("verified; apply skipped: another repair is applying to "
                "this sidecar — rerun to apply")
    try:
        try:
            live = source_path.read_text()
        except OSError:
            live = None
        if live != expected_source:
            return ("verified for the source as of repair start; apply "
                    "skipped: the source changed during this repair — rerun")
        current = user_sidecar.read_text() if user_sidecar.exists() else None
        if current == text:
            return "verified (sidecar already up to date)"
        if current != expected_prior:
            return ("verified; apply skipped: the sidecar changed during "
                    "this repair (a concurrent repair applied) — rerun to "
                    "reconcile")
        if current is not None:
            bak = user_sidecar.with_name(user_sidecar.name + ".bak")
            if not bak.exists():
                bak.write_text(current)
        tmp = tempfile.NamedTemporaryFile(
            "w", dir=user_sidecar.parent, prefix=user_sidecar.name + ".",
            suffix=".tmp", delete=False)
        with tmp:
            tmp.write(text)
        os.replace(tmp.name, user_sidecar)
        return "verified (sidecar applied)"
    finally:
        os.close(fd)  # dropping the fd releases the flock


@dataclass
class RepairOutcome:
    verified: bool
    iterations: int
    reason: str
    sidecar_text: str | None = None
    history: list[dict[str, Any]] = field(default_factory=list)
    # Telemetry: one record per verify, with the engine call that followed
    # it (if any) — {attempt, status, failure_kinds, verify_ms, engine_ms,
    # rejection}. `rejection` classifies a proposal the sidecar whitelist
    # would refuse ({rule, message}), counted at proposal time so the LAST
    # proposal of an exhausted budget is counted too (it never gets a
    # next-iteration payload).
    attempts: list[dict[str, Any]] = field(default_factory=list)


def _classify_rejection(proposal: str, name: str) -> dict[str, Any] | None:
    try:
        validate_sidecar_text(proposal, name)
    except EncodeError as exc:
        return {"rule": exc.rule or "other", "message": exc.message}
    return None


def _repairable(payload: dict[str, Any]) -> bool:
    """A proof edit can help with failed proofs and sidecar-validation
    rejections — not with spec errors or source-conformance rejections."""
    if payload["status"] == "failed":
        return True
    if payload["status"] == "encode-error":
        return any("proof sidecar" in (f.get("message") or "")
                   or "proof clause" in (f.get("message") or "")
                   for f in payload["failures"])
    return False


def repair_file(path: Path, outdir: Path, engine: Engine,
                max_iterations: int = 4, time_limit: int = 30,
                apply: bool = False) -> RepairOutcome:
    outdir.mkdir(parents=True, exist_ok=True)
    # A fresh private work directory per invocation: two overlapping
    # repairs of same-named sources sharing an outdir must never verify
    # (or apply) each other's files.
    work = Path(tempfile.mkdtemp(prefix="work-", dir=outdir))
    work_src = work / path.name
    work_src.write_text(path.read_text())
    user_sidecar = path.with_name(path.stem + ".proofs.dfy")
    initial_sidecar = user_sidecar.read_text() if user_sidecar.exists() else None
    work_sidecar = work / f"{path.stem}.proofs.dfy"
    if user_sidecar.exists():
        work_sidecar.write_text(user_sidecar.read_text())
    else:
        # A reused workdir may hold a previous run's sidecar; verifying
        # against it would fake iteration-zero success (and --apply would
        # write stale proof content beside the source).
        work_sidecar.unlink(missing_ok=True)
    source = work_src.read_text()
    history: list[dict[str, Any]] = []
    attempts: list[dict[str, Any]] = []

    for attempt in range(max_iterations + 1):
        t0 = time.monotonic()
        payload = verify_structured(work_src, work / f"iter{attempt}",
                                    time_limit=time_limit)
        record: dict[str, Any] = {
            "attempt": attempt,
            "status": payload["status"],
            "failure_kinds": sorted({f.get("kind") or "?"
                                     for f in payload["failures"]}),
            "verify_ms": int((time.monotonic() - t0) * 1000),
            "engine_ms": None,
            "rejection": None,
        }
        attempts.append(record)
        if payload["status"] == "ok":
            text = work_sidecar.read_text() if work_sidecar.exists() else None
            if apply and text is not None:
                reason = _apply_sidecar(user_sidecar, text, initial_sidecar,
                                        path, source)
                return RepairOutcome(True, attempt, reason, text, history,
                                     attempts)
            return RepairOutcome(True, attempt, "verified", text, history,
                                 attempts)
        if not _repairable(payload):
            return RepairOutcome(False, attempt,
                                 f"not repairable by proof edits: "
                                 f"{payload['status']}", None, history,
                                 attempts)
        if attempt == max_iterations:
            break
        request = build_request(source, payload, attempt, history)
        t1 = time.monotonic()
        try:
            proposal = _strip_fences(engine(request))
        except Exception as exc:
            return RepairOutcome(False, attempt, f"engine error: {exc}",
                                 None, history, attempts)
        record["engine_ms"] = int((time.monotonic() - t1) * 1000)
        record["rejection"] = _classify_rejection(proposal, work_sidecar.name)
        work_sidecar.write_text(proposal)
        history.append({
            "attempt": attempt,
            "failures": payload["failures"],
            "proposal": proposal,
        })
    return RepairOutcome(False, max_iterations, "iteration budget exhausted",
                         None, history, attempts)
