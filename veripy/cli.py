"""VeriPy CLI: check, emit, hunt, verify, guard, repair, benchmark, lsp."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from .frontend.conformance import RULES, aggregate, survey_paths
from .repair import ENGINE_EFFORT_LEVELS
from .frontend.extract import parse_source
from .frontend.typegate import run_type_gate
from .agentio import atomic_write_text, stub_dir_for
from .backends.dafny.driver import verify_dafny_file
from .backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar
from .backends.runtime.emit import emit_checked
from .hints import proof_hint

def _engine_wall(value: str) -> int:
    """argparse type for --engine-wall: a positive number of seconds.

    A non-positive wall can only be a mistake, and each kind used to fail
    quietly in its own way: a negative one reached `subprocess.run(timeout=)`
    and raised TimeoutExpired before the engine ran at all (an UNMEASURED
    task that reads like an engine that did not answer), and `0` was eaten by
    boolean defaulting and silently became 600s. Rejecting here means the
    wall an exam reports is the wall it ran under."""
    try:
        seconds = int(value)
    except ValueError:
        raise argparse.ArgumentTypeError(f"{value!r} is not an integer")
    if seconds <= 0:
        raise argparse.ArgumentTypeError(
            f"must be a positive number of seconds, got {seconds}")
    return seconds


def _effort(args) -> str | None:
    return getattr(args, "engine_effort", None)


def _wall(args) -> int:
    """The engine wall for this invocation (unset -> the default)."""
    from .repair import DEFAULT_ENGINE_WALL_S

    wall = getattr(args, "engine_wall", None)
    # `is None`, not `or`: an explicit value must never be defaulted away.
    return DEFAULT_ENGINE_WALL_S if wall is None else wall


_NOT_ENFORCED = ("invariant", "decreases", "proof")


def _report(path: Path) -> int:
    """Print a per-function spec report; return the number of errors."""
    specs = parse_source(path.read_text(), filename=str(path))
    errors = 0
    print(f"{path}")
    if not specs.functions and not specs.orphans:
        # "(no #@ specs found)" was the whole message, which tells a
        # newcomer nothing: not whether this file is even a candidate, and
        # not what to write. Name the functions the fragment would accept
        # — that is the actionable half, and it is already computable.
        print("  (no #@ specs found)")
        candidates = _fragment_candidates(path)
        if candidates:
            names = ", ".join(candidates)
            print(f"  in-fragment and ready to annotate: {names}")
            print(f"  add `#@ ensures <property of result>` directly above "
                  f"`def {candidates[0]}` — see docs/SPEC-GRAMMAR.md")
        return 0
    for fn in specs.functions:
        tag = " [verified]" if fn.verified else ""
        print(f"  {fn.name} (line {fn.lineno}){tag}")
        for c in fn.clauses:
            if c.kind == "verified":
                continue
            if c.error is not None:
                errors += 1
                print(f"    line {c.line}: ERROR in `{c.kind} {c.raw}`: {c.error}")
            elif c.kind in _NOT_ENFORCED:
                print(f"    line {c.line}: {c.kind} {c.raw}  (recorded; not enforced in M0)")
            else:
                print(f"    line {c.line}: {c.kind} {c.raw}")
                print(f"      -> {c.desugared}")
    for c in specs.orphans:
        errors += 1
        print(f"  line {c.line}: ERROR: {c.error}")
    return errors


def _fragment_candidates(path: Path) -> list[str]:
    """Module-level functions the fragment would accept if they carried
    specs. Annotating one is the newcomer's next action, so `check` should
    say which ones qualify rather than leaving them to guess."""
    import ast as _ast

    from .backends.dafny.encoder import EncodeError, encode_module
    from .frontend.parse import Clause, FunctionSpec, ModuleSpecs

    try:
        source = path.read_text()
        tree = _ast.parse(source)
    except (OSError, UnicodeDecodeError, SyntaxError, ValueError):
        return []
    ready: list[str] = []
    for node in tree.body:
        if not isinstance(node, _ast.FunctionDef):
            continue
        if node.decorator_list:
            # X-DECOR: the fragment excludes decorated functions ("function
            # surgery" — the decorator replaces the function object, so the
            # body Dafny verifies is not what runs). The encoder probe below
            # cannot see this: it encodes the body and never looks at the
            # decorator list, so it would happily report a candidate. Two
            # things would then go wrong at once — the user is sent to
            # annotate a function outside the fragment, and the placement
            # advice is wrong for it besides, since a contract block must sit
            # above the FIRST DECORATOR, not above the `def`.
            continue
        # A trivial `ensures True` is enough to ask the encoder "would you
        # take this body?" without inventing a property for the user.
        probe = FunctionSpec(
            name=node.name, lineno=node.lineno, anchor_lineno=node.lineno,
            params=tuple(a.arg for a in node.args.args),
            clauses=[Clause(kind="ensures", raw="True", line=node.lineno,
                            desugared="True")])
        try:
            encode_module(source, ModuleSpecs(functions=[probe], orphans=[]),
                          module_name=path.name)
        except EncodeError:
            continue  # outside the fragment: not a candidate, correctly
        except (OSError, UnicodeDecodeError, ValueError):
            continue
        # Deliberately NOT a bare `except`: this is advisory output, but
        # swallowing every exception would turn a genuine encoder bug into
        # a silently shorter list, which is the hardest kind to notice.
        ready.append(node.name)
    return ready


def _fragment_check(path: Path) -> int:
    """Dry-run the Dafny encoder on each spec'd function — the encoder is
    the single conformance authority, so `check` reports exactly what
    `verify` would reject, without needing Dafny installed."""
    from .backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar

    source = path.read_text()
    specs = parse_source(source, filename=str(path))
    if specs.errors or specs.orphans or not specs.functions:
        return 0  # spec diagnostics were already reported by _report
    try:
        sidecar = load_proof_sidecar(path)
        encode_module(source, specs, module_name=path.name,
                      proof_lemmas=sidecar.lemmas)
    except EncodeError as e:
        loc = f"{path}:{e.line}" if e.line else str(path)
        print(f"  fragment: {loc}: {e.message}")
        return 1
    except (OSError, UnicodeDecodeError) as e:
        # An unreadable/undecodable proof sidecar is a controlled check
        # failure, not a traceback.
        print(f"  fragment: {path}: unreadable proof sidecar: {e}")
        return 1
    names = ", ".join(fn.name for fn in specs.functions)
    print(f"  fragment: conformant ({names})")
    return 0


def cmd_check(paths: list[Path], types: bool = True, fragment: bool = True) -> int:
    total_errors = 0
    for path in paths:
        total_errors += _report(path)
        if fragment:
            total_errors += _fragment_check(path)

    if types:
        gate = run_type_gate(paths)
        if not gate.available:
            # An unrunnable gate is a failure, not a pass — skipping type
            # analysis must be an explicit choice (--no-types).
            print(
                f"\ntype gate: FAILED to run ({gate.error}); "
                f"pass --no-types to skip type checking explicitly",
                file=sys.stderr,
            )
            total_errors += 1
        else:
            print(
                f"\ntype gate (basedpyright {gate.version or '?'}): "
                f"{len(gate.errors)} error(s), {len(gate.warnings)} warning(s)"
            )
            cwd = Path.cwd()
            for d in gate.diagnostics:
                file = Path(d.file)
                try:
                    file = file.relative_to(cwd)
                except ValueError:
                    pass
                rule = f"  [{d.rule}]" if d.rule else ""
                print(f"  {file}:{d.line} {d.severity}: {d.message}{rule}")
            total_errors += len(gate.errors)

    if total_errors:
        print(f"\n{total_errors} error(s).", file=sys.stderr)
        return 1
    return 0


def cmd_emit(paths: list[Path], outdir: Path) -> int:
    # Distinct inputs with the same stem would overwrite each other's
    # emitted module (and hunt would then analyze the survivor under every
    # original label) — fail closed instead.
    by_stem: dict[str, list[Path]] = {}
    for path in paths:
        by_stem.setdefault(path.stem, []).append(path)
    collisions = {stem: ps for stem, ps in by_stem.items() if len(ps) > 1}
    if collisions:
        for stem, ps in collisions.items():
            print(
                f"emit: output name collision — {', '.join(map(str, ps))} would all "
                f"emit {stem}_checked.py; emit them separately or into distinct --outdir",
                file=sys.stderr,
            )
        return 1

    outdir.mkdir(parents=True, exist_ok=True)
    status = 0
    for path in paths:
        source = path.read_text()
        specs = parse_source(source, filename=str(path))
        if specs.errors or specs.orphans:
            print(f"{path}: spec errors; run `veripy check` first", file=sys.stderr)
            status = 1
            continue
        checked = emit_checked(source, specs, src_name=path.name)
        out_path = outdir / f"{path.stem}_checked.py"
        out_path.write_text(checked)
        print(f"{path} -> {out_path}")
    return status


def cmd_survey(paths: list[Path], top: int, json_out: Path | None) -> int:
    reports = survey_paths(paths)
    stats = aggregate(reports)
    print(
        f"files={stats['files']} (errors={stats['file_errors']})  "
        f"functions={stats['functions']}  "
        f"accepted={stats['accepted']} ({stats['accepted_pct']}%)  "
        f"loc-accepted={stats['accepted_loc']}/{stats['loc']} ({stats['accepted_loc_pct']}%)"
    )
    if stats["rule_counts"]:
        print(f"\ntop {min(top, len(stats['rule_counts']))} rules by fire count:")
        for rule_id, count in list(stats["rule_counts"].items())[:top]:
            rule = RULES.get(rule_id)
            title = f"{rule.title}  [{rule.ref}]" if rule else "?"
            print(f"  {rule_id:<16} {count:>7}   {title}")
    if json_out is not None:
        payload = {
            "aggregate": stats,
            "files": [
                {
                    "path": r.path,
                    "error": r.error,
                    "file_fires": [
                        {"rule": f.rule, "line": f.line, "detail": f.detail}
                        for f in r.file_fires
                    ],
                    "functions": [
                        {
                            "qualname": fn.qualname,
                            "line": fn.lineno,
                            "loc": fn.loc,
                            "accepted": fn.accepted,
                            "fires": [
                                {"rule": f.rule, "line": f.line, "detail": f.detail}
                                for f in fn.fires
                            ],
                        }
                        for fn in r.functions
                    ],
                }
                for r in reports
            ],
        }
        json_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(payload, indent=1))
        print(f"\nfull report -> {json_out}")
    return 0


def _find_crosshair() -> str | None:
    exe = shutil.which("crosshair")
    if exe:
        return exe
    candidate = Path(sys.executable).parent / "crosshair"
    return str(candidate) if candidate.exists() else None


def cmd_hunt(paths: list[Path], outdir: Path, per_condition_timeout: int) -> int:
    """Emit checked modules and let CrossHair hunt for counterexamples."""
    status = cmd_emit(paths, outdir)
    if status:
        return status
    exe = _find_crosshair()
    if exe is None:
        print(
            "hunt: crosshair not found — install with `pip install 'veripy[dev]'`",
            file=sys.stderr,
        )
        return 2
    findings = 0
    trouble = 0
    for path in paths:
        checked = outdir / f"{path.stem}_checked.py"
        cmd = [
            exe, "check", str(checked),
            "--analysis_kind", "icontract",
            "--per_condition_timeout", str(per_condition_timeout),
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        output = (proc.stdout + proc.stderr).strip()
        # CrossHair exit codes: 0 = clean, 1 = counterexamples, 2 = error.
        if proc.returncode == 0:
            print(f"{path}: no counterexamples found")
        elif proc.returncode == 1:
            findings += 1
            print(f"{path}: COUNTEREXAMPLE")
            for line in output.splitlines():
                print(f"  {line}")
        else:
            trouble += 1
            print(f"{path}: crosshair exited {proc.returncode}", file=sys.stderr)
            for line in output.splitlines():
                print(f"  {line}", file=sys.stderr)
    if trouble:
        return 2
    return 1 if findings else 0


def cmd_verify(paths: list[Path], outdir: Path, time_limit: int, types: bool = True,
               report: Path | None = None) -> int:
    """Encode to Dafny and verify: the M1 pipeline (clean-bucket fragment)."""
    from .backends.dafny.driver import dafny_version
    from .report import build_report, function_report, render_report_text

    outdir.mkdir(parents=True, exist_ok=True)
    failed = 0
    trouble = 0
    fn_reports: list = []
    sidecar_lemmas: dict[str, list[str]] = {}
    if types:
        # The A7 first pass applies to verification too: an untyped or
        # ill-typed file must not reach the encoder.
        gate = run_type_gate(paths)
        if not gate.available:
            print(
                f"type gate: FAILED to run ({gate.error}); "
                f"pass --no-types to skip type checking explicitly",
                file=sys.stderr,
            )
            return 2
        if gate.errors:
            for d in gate.errors:
                print(f"{d.file}:{d.line} {d.severity}: {d.message}", file=sys.stderr)
            print(f"type gate: {len(gate.errors)} error(s); nothing verified", file=sys.stderr)
            return 2
    for path in paths:
        source = path.read_text()
        specs = parse_source(source, filename=str(path))
        if specs.errors or specs.orphans:
            print(f"{path}: spec errors; run `veripy check` first", file=sys.stderr)
            trouble += 1
            fn_reports += [function_report(fn, str(path), "error") for fn in specs.functions]
            continue
        try:
            sidecar = load_proof_sidecar(path)
            encoded = encode_module(
                source, specs, module_name=path.name, proof_lemmas=sidecar.lemmas
            )
        except EncodeError as exc:
            loc = f":{exc.line}" if exc.line is not None else ""
            print(f"{path}{loc}: cannot encode: {exc.message}", file=sys.stderr)
            trouble += 1
            fn_reports += [function_report(fn, str(path), "error") for fn in specs.functions]
            continue
        except (OSError, UnicodeDecodeError) as exc:
            print(f"{path}: unreadable proof sidecar: {exc}", file=sys.stderr)
            trouble += 1
            fn_reports += [function_report(fn, str(path), "error") for fn in specs.functions]
            continue
        if sidecar.lemmas:
            sidecar_lemmas[str(path)] = sorted(sidecar.lemmas)
        # Private staging per file: `outdir/<stem>.dfy` made two concurrent
        # verifications of same-stemmed modules race on one path, and the
        # loser's verdict was reported against the winner's stub — silently,
        # in both directions. See verify_structured for the full note.
        # Content-addressed because this path KEEPS its artifacts (the paths
        # below are printed for a human to open), so re-running the same
        # file must overwrite rather than leave a directory per run.
        stub_text = encoded.dafny_source + sidecar.text
        stub_dir = stub_dir_for(outdir, path, stub_text)
        stub_dir.mkdir(parents=True, exist_ok=True)
        stub = stub_dir / f"{path.stem}.dfy"
        atomic_write_text(stub, stub_text)
        stub_extent = encoded.dafny_source.count("\n") + 1
        result = verify_dafny_file(stub, encoded.line_map,
                                   time_limit=time_limit,
                                   stub_extent=stub_extent)
        if result.error is not None:
            print(f"{path}: dafny trouble: {result.error}", file=sys.stderr)
            trouble += 1
            fn_reports += [function_report(fn, str(path), "error") for fn in specs.functions]
            continue
        if result.ok:
            print(f"{path}: VERIFIED ({', '.join(encoded.methods)}) -> {stub}")
            fn_reports += [function_report(fn, str(path), "verified") for fn in specs.functions]
        else:
            failed += 1
            print(f"{path}: VERIFICATION FAILED -> {stub}")
            errs = []
            for d in result.diagnostics:
                if d.severity == "error":
                    # A failure in the appended sidecar region gets a
                    # PYTHON line from the driver's nearest-mapping lookup,
                    # which sends the reader to a line that has nothing to
                    # do with the failing lemma. The structured payload has
                    # always said `region: "sidecar"`; the printed line
                    # disagreed with it. Name the .proofs.dfy file and its
                    # own line number instead.
                    at = sidecar.locate(d.dafny_line, stub_extent)
                    if at is not None:
                        where = f"{at[0]}:{at[1]}"
                    elif d.py_line is not None and d.dafny_line <= stub_extent:
                        where = f"{path}:{d.py_line}"
                    else:
                        where = f"{stub}:{d.dafny_line}"
                    print(f"  {where}: {d.message}")
                    hint = proof_hint(d, source, specs)
                    if hint:
                        print(f"    hint: {hint}")
                    errs.append(d)
            # Attribute failures to the enclosing function by source span.
            # Failures in the appended sidecar region (beyond the stub) or
            # with no mapped Python line belong to no span; they must not
            # let the other functions read as verified.
            unattributed = [d for d in errs
                            if d.py_line is None or d.dafny_line > stub_extent]
            attributable = [d for d in errs if d not in unattributed]
            spans = sorted(specs.functions, key=lambda f: f.lineno)
            for i, fn in enumerate(spans):
                hi = spans[i + 1].lineno if i + 1 < len(spans) else 10**9
                mine = [d for d in attributable
                        if d.py_line is not None and fn.lineno <= d.py_line < hi]
                fails = [{"file": str(path), "line": d.py_line, "message": d.message}
                         for d in mine]
                if not mine and unattributed:
                    status_str = "indeterminate"
                    fails = []
                    for d in unattributed:
                        at = sidecar.locate(d.dafny_line, stub_extent)
                        if at is not None:
                            fails.append({"file": at[0], "line": at[1],
                                          "message": f"proof sidecar: {d.message}"})
                        else:
                            fails.append({"file": str(stub), "line": d.dafny_line,
                                          "message": f"unattributed (generated "
                                                     f"region): {d.message}"})
                else:
                    status_str = "failed" if mine else "verified"
                fn_reports.append(function_report(fn, str(path), status_str, fails))
    if report is not None:
        payload = build_report(fn_reports, sidecar_lemmas, dafny_version())
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text(json.dumps(payload, indent=1))
        print(f"\n{render_report_text(payload)}")
        print(f"\nreport -> {report}")
    if trouble:
        return 2
    return 1 if failed else 0


# Directories that hold code nobody wrote as corpus: dependencies, build
# output, caches. Sweeping them is not merely slow — every third-party file
# lands in the report as "trouble" or as compared functions, and `compared`
# is exactly the number `--min-functions` is measured against, so a floor
# meant to prove the corpus is still covered could be satisfied entirely by
# whatever happens to be vendored into the tree.
_SWEEP_PRUNED = frozenset({
    "__pycache__", "node_modules", "site-packages", "build", "dist",
    "venv", "env",
})


def _swept(root: Path, file: Path) -> bool:
    """Is `file` corpus, or is it something that landed under `root`?"""
    rel = file.relative_to(root).parts
    # Hidden at any depth: `.venv/lib/.../x.py` is not hidden by filename,
    # only by the directory it sits in.
    return not any(part.startswith(".") or part in _SWEEP_PRUNED
                   or part.endswith(".egg-info") for part in rel)


def _difftest_targets(paths: list[Path]) -> list[Path]:
    """Expand directories to the `.py` files under them.

    A nightly sweep is pointed at a corpus, not at a hand-written file
    list — a list goes stale silently the moment a task is added, which is
    the failure mode this whole command exists to prevent.

    Pruning applies to directory expansion only: a file named on the command
    line is swept wherever it lives, because naming it is the intent.
    """
    targets: list[Path] = []
    for path in paths:
        if path.is_dir():
            targets.extend(sorted(p for p in path.rglob("*.py")
                                  if _swept(path, p)))
        else:
            targets.append(path)
    # A file reachable twice (listed AND inside a listed directory) would
    # otherwise be compared twice and counted twice.
    seen: set[Path] = set()
    unique = []
    for path in targets:
        key = path.resolve()
        if key not in seen:
            seen.add(key)
            unique.append(path)
    return unique


def cmd_difftest(paths: list[Path], outdir: Path, examples: int,
                 report: Path | None = None, min_functions: int = 1) -> int:
    """Translation validation (§6): original Python vs Dafny-compiled model."""
    from .difftest.harness import difftest_file

    diverged = 0
    trouble = 0
    compared = 0
    skipped: list[str] = []
    files: list[dict] = []
    targets = _difftest_targets(paths)
    for path in targets:
        result = difftest_file(path, outdir, examples=examples)
        entry: dict = {"path": str(path), "error": result.error, "functions": []}
        files.append(entry)
        if result.error:
            print(f"{path}: difftest trouble: {result.error}", file=sys.stderr)
            trouble += 1
            continue
        if not result.functions:
            # NOT silent: a file with nothing to compare used to print
            # nothing and leave the exit code at 0, so a sweep that had
            # quietly stopped covering anything looked exactly like a
            # sweep that passed.
            skipped.append(str(path))
            print(f"{path}: no spec'd functions — nothing to compare")
            continue
        for fn in result.functions:
            record = {"name": fn.name, "examples": fn.examples,
                      "ok": fn.ok, "error": fn.error, "mismatch": None}
            entry["functions"].append(record)
            if fn.ok:
                compared += 1
                print(f"{path}::{fn.name}: OK ({fn.examples} examples)")
            elif fn.mismatch is not None:
                diverged += 1
                compared += 1
                m = fn.mismatch
                # reprs, not the values: this record is the REPRODUCER, and
                # it has to survive JSON for objects that may not.
                record["mismatch"] = {"args": repr(m.args),
                                      "python": repr(m.python_result),
                                      "dafny": repr(m.dafny_result)}
                print(f"{path}::{fn.name}: DIVERGENCE (encoder bug)")
                print(f"  args={m.args!r}")
                print(f"  python={m.python_result!r}  dafny-model={m.dafny_result!r}")
            else:
                trouble += 1
                print(f"{path}::{fn.name}: trouble: {fn.error}", file=sys.stderr)

    print(f"\n{compared} function(s) compared at {examples} examples across "
          f"{len(targets)} file(s); {len(skipped)} with nothing to compare, "
          f"{diverged} diverged, {trouble} trouble")
    if report is not None:
        payload = {
            "schema": "veripy-difftest/1",
            "examples": examples,
            "files": files,
            "totals": {"files": len(targets), "compared": compared,
                       "skipped": len(skipped), "diverged": diverged,
                       "trouble": trouble},
        }
        try:
            report.parent.mkdir(parents=True, exist_ok=True)
            # ATOMIC: `write_text` truncates first, so a failure part-way
            # through leaves invalid JSON at the final path — and the
            # nightly's upload step runs `if: always()`, so it would
            # publish that unusable file in place of the reproducer. The
            # report either appears whole or does not appear.
            atomic_write_text(report, json.dumps(payload, indent=1))
            print(f"report -> {report}")
        except OSError as exc:
            # The sweep's verdict must outlive a bad --report path. Letting
            # this raise threw away the exit code the whole command exists
            # to produce, and an uncaught exception exits 1 — the code that
            # means DIVERGENCE, so an unwritable directory would have been
            # read as an encoder bug (or, on a run that had diverged, would
            # have suppressed the summary the next steps read).
            print(f"could not write the difftest report to {report}: {exc}",
                  file=sys.stderr)
            trouble += 1
    if diverged:
        return 1
    if compared < min_functions:
        # The vacuity guard. A sweep that compared less than it was told to
        # expect has not passed — it has stopped testing, and green is the
        # most dangerous thing it could report.
        print(f"difftest compared {compared} function(s), expected at least "
              f"{min_functions} — the sweep is not covering what it should",
              file=sys.stderr)
        return 2
    return 2 if trouble else 0


def cmd_screen(tasks: Path, time_limit: int = 60) -> int:
    """Report whether each task's proof pack is load-bearing — the gate a
    candidate must clear before joining the exam roster."""
    from .benchmark.exam import exam_tasks, render_screen_report, screen_sidecar

    results = [screen_sidecar(d, time_limit=time_limit)
               for d in exam_tasks(tasks)]
    print(render_screen_report(results))
    if not results:
        print(f"no sidecar-bearing tasks under {tasks}", file=sys.stderr)
        return 2
    return 0 if all(r.adoptable for r in results) else 1


def cmd_benchmark(tasks: Path, outdir: Path, report: Path | None,
                 mutant_cap: int, quick: bool) -> int:
    from .benchmark.runner import ERROR, FAIL, render_report, run_benchmark, scores_to_json

    kwargs = dict(mutant_cap=mutant_cap, hunt_timeout=5,
                  dafny_time_limit=60, difftest_examples=60)
    if quick:
        kwargs.update(mutant_cap=min(mutant_cap, 4), difftest_examples=20)
    scores = run_benchmark(tasks, outdir, **kwargs)
    if not scores:
        print(f"no tasks found under {tasks}", file=sys.stderr)
        return 2
    print(render_report(scores))
    if report is not None:
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text(json.dumps(scores_to_json(scores), indent=1))
        print(f"\nreport -> {report}")
    # Exit status mirrors the scorecard so CI can gate on it: 2 for an
    # incomplete run (tool errors), 1 for a regression (failed rungs).
    if any(r.status == ERROR for s in scores for r in s.rungs):
        return 2
    if any(r.status == FAIL for s in scores for r in s.rungs):
        return 1
    return 0


def cmd_guard(paths: list[Path], outdir: Path, check_ensures: bool = False) -> int:
    from .guards.emitter import GuardGenError, emit_guarded

    by_stem: dict[str, list[Path]] = {}
    for path in paths:
        by_stem.setdefault(path.stem, []).append(path)
    collisions = {stem: ps for stem, ps in by_stem.items() if len(ps) > 1}
    if collisions:
        for stem, ps in collisions.items():
            print(f"stem collision {stem!r}: {', '.join(map(str, ps))}", file=sys.stderr)
        return 2
    status = 0
    outdir.mkdir(parents=True, exist_ok=True)
    for path in paths:
        source = path.read_text()
        specs = parse_source(source, filename=str(path))
        if specs.errors or specs.orphans:
            print(f"{path}: spec errors — fix them before guarding", file=sys.stderr)
            status = 1
            continue
        try:
            guarded = emit_guarded(source, specs, src_name=path.name,
                                   check_ensures=check_ensures)
        except GuardGenError as e:
            loc = f"{path}:{e.line}" if e.line else str(path)
            print(f"{loc}: cannot guard: {e.message}", file=sys.stderr)
            status = 1
            continue
        out = outdir / f"{path.stem}_guarded.py"
        out.write_text(guarded)
        names = ", ".join(fn.name for fn in specs.functions)
        print(f"{path} -> {out} (guarded: {names})")
        unmarked = [fn.name for fn in specs.functions if not fn.verified]
        if unmarked:
            print(
                f"  note: not marked #@ verified (guards enforce the written "
                f"spec; proof status comes from `veripy verify`): "
                f"{', '.join(unmarked)}"
            )
    return status


def cmd_repair(path: Path, outdir: Path, engine_spec: str, max_iterations: int,
               time_limit: int, apply: bool, engine_wall: int | None = None,
               engine_effort: str | None = None) -> int:
    from .repair import DEFAULT_ENGINE_WALL_S, make_engine, repair_file

    wall = DEFAULT_ENGINE_WALL_S if engine_wall is None else engine_wall
    try:
        engine = make_engine(engine_spec, wall, effort=engine_effort)
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 2
    outcome = repair_file(path, outdir, engine, max_iterations=max_iterations,
                          time_limit=time_limit, apply=apply)
    if outcome.verified:
        detail = f" — {outcome.reason}" if outcome.reason != "verified" else ""
        print(f"{path}: VERIFIED after {outcome.iterations} repair "
              f"iteration(s){detail}")
        return 0
    print(f"{path}: NOT verified — {outcome.reason} "
          f"({outcome.iterations} iteration(s))", file=sys.stderr)
    return 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="veripy",
        description="Verify a typed Python fragment (#@ specs). "
                    "M0: runtime contracts + CrossHair counterexamples.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_check = sub.add_parser(
        "check",
        help="parse #@ specs, report diagnostics, check fragment conformance; "
             "gates on basedpyright",
    )
    p_check.add_argument("files", nargs="+", type=Path)
    p_check.add_argument(
        "--no-types",
        action="store_true",
        help="skip the basedpyright type gate",
    )
    p_check.add_argument(
        "--no-fragment",
        action="store_true",
        help="skip the fragment-conformance dry-run of the Dafny encoder",
    )

    p_emit = sub.add_parser("emit", help="emit icontract-checked copies of modules")
    p_emit.add_argument("files", nargs="+", type=Path)
    p_emit.add_argument("-o", "--outdir", type=Path, default=Path("build/checked"))

    p_guard = sub.add_parser(
        "guard",
        help="emit guarded sibling modules: deep type checks + copy-in + "
             "executable requires at the boundary (ARCHITECTURE §4)",
    )
    p_guard.add_argument("files", nargs="+", type=Path)
    p_guard.add_argument("-o", "--outdir", type=Path, default=Path("build/guarded"))
    p_guard.add_argument(
        "--check-ensures",
        action="store_true",
        help="also evaluate ensures clauses at runtime (blame: callee-or-toolchain)",
    )

    p_hunt = sub.add_parser(
        "hunt",
        help="emit checked modules and search for counterexamples with CrossHair",
    )
    p_hunt.add_argument("files", nargs="+", type=Path)
    p_hunt.add_argument("-o", "--outdir", type=Path, default=Path("build/checked"))
    p_hunt.add_argument("--per-condition-timeout", type=int, default=20)

    p_verify = sub.add_parser(
        "verify",
        help="encode the fragment to Dafny and verify (M1 clean-bucket slice)",
    )
    p_verify.add_argument("files", nargs="+", type=Path)
    p_verify.add_argument("-o", "--outdir", type=Path, default=Path("build/dafny"))
    p_verify.add_argument("--time-limit", type=int, default=30)
    p_verify.add_argument("--no-types", action="store_true", help="skip the basedpyright type gate")
    p_verify.add_argument(
        "--report", type=Path, default=None,
        help="write the verification report (per-function verdicts, "
             "assumptions A1-A7, guard modes) as JSON",
    )
    p_verify.add_argument(
        "--json", type=Path, default=None, dest="json_out",
        help="write structured failures (obligation kind, spans, sidecar "
             "state) — the agent interface consumed by `veripy repair`",
    )
    p_verify.add_argument(
        "--hunt-counterexamples", action="store_true",
        help="with --json: run CrossHair on failing modules to attach a "
             "concrete counterexample when one exists",
    )
    from .backends.base import available_backends

    p_verify.add_argument(
        "--backend", choices=available_backends(), default="dafny",
        help="proof backend (the ROADMAP's Lean track lands behind this "
             "flag; a typo is refused, never silently substituted)",
    )

    p_difftest = sub.add_parser(
        "difftest",
        help="differentially test original Python vs the Dafny-compiled model (§6)",
    )
    p_difftest.add_argument("files", nargs="+", type=Path)
    p_difftest.add_argument("-o", "--outdir", type=Path, default=Path("build/difftest"))
    p_difftest.add_argument("-n", "--examples", type=int, default=100)
    p_difftest.add_argument("--report", type=Path,
                            help="write a machine-readable divergence report "
                                 "(JSON) — what a nightly sweep uploads")
    p_difftest.add_argument("--min-functions", type=int, default=1,
                            help="fail unless at least N functions were "
                                 "actually compared (default 1: a sweep that "
                                 "compared nothing has not passed)")

    p_benchmark = sub.add_parser(
        "benchmark",
        help="run veripy-benchmark: assurance-ladder scoring over annotated-Python tasks",
    )
    p_benchmark.add_argument("--tasks", type=Path, default=Path("benchmark/tasks"))
    p_benchmark.add_argument("-o", "--outdir", type=Path, default=Path("build/benchmark"))
    p_benchmark.add_argument("--report", type=Path, default=None)
    p_benchmark.add_argument("--mutant-cap", type=int, default=12)
    p_benchmark.add_argument(
        "--exam", choices=["proof-repair", "spec-writing"], default=None,
        help="run an exam instead of the ladder: 'proof-repair' strips the "
             "proof additions and scores restoration under frozen specs; "
             "'spec-writing' strips the SPECS and scores the strength of "
             "the ones the engine writes (mutant kill rate vs golden)",
    )
    p_benchmark.add_argument(
        "--engine-effort", choices=list(ENGINE_EFFORT_LEVELS), default=None,
        help="claude-CLI reasoning effort for engine calls; omitted = the "
             "CLI default, recorded as such")
    parser.add_argument(
        "--engine-wall", type=_engine_wall, default=None,
        help="seconds a single engine call may take (default 600); raise it "
             "to tell 'could not prove it' apart from 'did not answer'",
    )
    p_benchmark.add_argument(
        "--engine", default="claude",
        help="engine for --exam (claude | claude:<model> | "
             "api:<provider>/<model> | file:<dir>)",
    )
    p_benchmark.add_argument(
        "--retries", type=int, default=2,
        help="with --exam spec-writing: retries allowed for a MECHANICALLY "
             "invalid answer (unparseable, freeze violation, bad clause)",
    )
    p_benchmark.add_argument(
        "--screen", action="store_true",
        help="report whether each task's proof pack is LOAD-BEARING (the "
             "gate for joining the exam roster) instead of running the "
             "ladder; exits 1 if any pack is vacuous or unscreenable")
    p_benchmark.add_argument("--quick", action="store_true",
                            help="small mutant panels and example counts (CI mode)")
    p_benchmark.add_argument("--max-iterations", type=int, default=4,
                             help="with --exam: repair-loop iteration budget")
    p_benchmark.add_argument("--time-limit", type=int, default=60,
                             help="with --exam: prover time limit per attempt (s)")

    p_experiment = sub.add_parser(
        "experiment",
        help="run an exam as a (task x engine x arm x trial) matrix with an "
             "append-only JSONL ledger; resumable",
    )
    p_experiment.add_argument("--tasks", type=Path, default=Path("benchmark/tasks"))
    p_experiment.add_argument("-o", "--outdir", type=Path,
                              default=Path("build/experiment"))
    p_experiment.add_argument("--engines", nargs="+", default=["claude"],
                              help="engine specs: claude | claude:<model> | "
                                   "api:<provider>/<model> | file:<dir>")
    p_experiment.add_argument("--exam", choices=["proof-repair", "spec-writing"],
                              default="proof-repair")
    p_experiment.add_argument("--arms", nargs="+", default=["full", "one-shot"],
                              help="full | one-shot | ablated "
                                   "(spec-writing supports one-shot only)")
    p_experiment.add_argument("--retries", type=int, default=2,
                              help="with --exam spec-writing: retries for a "
                                   "mechanically invalid answer")
    p_experiment.add_argument("--mutant-cap", type=int, default=12)
    p_experiment.add_argument("--trials", type=int, default=3)
    p_experiment.add_argument("--ledger", type=Path, default=None,
                              help="JSONL ledger path (default: <outdir>/ledger.jsonl)")
    p_experiment.add_argument("--max-iterations", type=int, default=4)
    p_experiment.add_argument("--time-limit", type=int, default=60)
    p_experiment.add_argument("--engine-wall", type=_engine_wall, default=None,
                              help="wall-clock seconds per ENGINE call before "
                                   "the harness gives up on it (default 600). "
                                   "Part of the invocation, not a tuning knob: "
                                   "exceeding it yields an UNMEASURED task, so "
                                   "runs differing in it are not comparable")
    p_experiment.add_argument("--task", action="append", default=None,
                              dest="only_tasks", metavar="TASK",
                              help="restrict to this task (repeatable)")
    p_experiment.add_argument("--no-resume", action="store_true",
                              help="re-run cells already in the ledger "
                                   "(appends; the newest row wins)")
    p_experiment.add_argument("--summarize", type=Path, default=None,
                              metavar="LEDGER",
                              help="print the summary table for an existing "
                                   "ledger and exit (no cells are run)")

    p_repair = sub.add_parser(
        "repair",
        help="LLM proof-repair loop: verify, feed structured failures to an "
             "engine that may edit ONLY the proof sidecar, re-verify, iterate",
    )
    p_repair.add_argument("file", type=Path)
    p_repair.add_argument("-o", "--outdir", type=Path, default=Path("build/repair"))
    p_repair.add_argument("--engine-wall", type=_engine_wall, default=None,
                          help="seconds a single engine call may take "
                               "(default 600)")
    p_repair.add_argument("--engine", default="claude",
                          help="'claude' (headless CLI) or 'file:<dir>' "
                               "(scripted attempts, for tests/replays)")
    p_repair.add_argument("--max-iterations", type=int, default=4)
    p_repair.add_argument("--time-limit", type=int, default=30)
    p_repair.add_argument("--apply", action="store_true",
                          help="on success, write the sidecar next to the "
                               "source (previous content saved as .bak)")

    sub.add_parser(
        "lsp",
        help="run the LSP server over stdio: instant conformance "
             "diagnostics + per-function status, and proof status on "
             "explicit request (docs/EDITOR.md)",
    )

    p_survey = sub.add_parser(
        "survey",
        help="read-only fragment-coverage survey over files/directories (M0, RQ1)",
    )
    p_survey.add_argument("paths", nargs="+", type=Path)
    p_survey.add_argument("--top", type=int, default=15)
    p_survey.add_argument("--json", type=Path, default=None)

    args = parser.parse_args(argv)
    if args.command == "check":
        return cmd_check(args.files, types=not args.no_types,
                         fragment=not args.no_fragment)
    if args.command == "emit":
        return cmd_emit(args.files, args.outdir)
    if args.command == "guard":
        return cmd_guard(args.files, args.outdir, check_ensures=args.check_ensures)
    if args.command == "hunt":
        return cmd_hunt(args.files, args.outdir, args.per_condition_timeout)
    if args.command == "verify":
        if args.json_out is not None:
            from .agentio import dump, verify_structured_many

            if not args.no_types:
                gate = run_type_gate(args.files)
                if not gate.available or gate.errors:
                    # The agent asked for JSON; a gate failure is still a
                    # structured payload, never a silent empty run.
                    by_file: dict[str, list] = {str(p): [] for p in args.files}
                    # basedpyright reports resolved paths; map diagnostics
                    # back to EVERY spelling the caller used for that file
                    # (m.py and ./m.py must both carry their diagnostics).
                    resolved: dict[str, list[str]] = {}
                    for p in args.files:
                        resolved.setdefault(str(Path(p).resolve()), []).append(str(p))
                    for d in (gate.errors if gate.available else []):
                        keys = resolved.get(str(Path(d.file).resolve()), [d.file])
                        for key in keys:
                            by_file.setdefault(key, []).append(
                                {"kind": "type", "py_line": d.line,
                                 "message": d.message})
                    from .agentio import new_payload

                    payloads = []
                    for f, fails in by_file.items():
                        entry = new_payload(f)
                        entry["status"] = "gate-error"
                        entry["failures"] = fails or (
                            [] if gate.available else
                            [{"kind": "type", "py_line": None,
                              "message": f"type gate unavailable: {gate.error}"}])
                        payloads.append(entry)
                    try:
                        dump(payloads, args.json_out)
                    except OSError as exc:
                        print(f"cannot write {args.json_out}: {exc}", file=sys.stderr)
                        return 2
                    print("type gate failed; structured payloads written to "
                          f"{args.json_out}; fix types or pass --no-types",
                          file=sys.stderr)
                    return 2
            # The CLI is a human-facing surface: keep the emitted stub so
            # the payload's `stub` path can actually be opened. A library
            # caller gets the cleaning default instead.
            payloads = verify_structured_many(
                args.files, args.outdir, time_limit=args.time_limit,
                hunt_counterexamples=args.hunt_counterexamples,
                keep_artifacts=True, backend=args.backend)
            try:
                dump(payloads, args.json_out)
            except OSError as exc:
                print(f"cannot write {args.json_out}: {exc}", file=sys.stderr)
                return 2
            for p in payloads:
                print(f"{p['file']}: {p['status']} ({len(p['failures'])} failure(s))")
            print(f"structured failures -> {args.json_out}")
            if any(p["status"] in ("tool-error", "spec-error", "encode-error")
                   for p in payloads):
                return 2
            return 1 if any(p["status"] == "failed" for p in payloads) else 0
        if args.backend != "dafny":
            # The human-report path still calls the Dafny encoder
            # directly. Refuse rather than silently verify under a
            # different backend than the one requested — same principle
            # as the engine layer's substitution guard.
            print(f"--backend {args.backend} requires --json (the "
                  f"human-report path is not yet backend-aware)",
                  file=sys.stderr)
            return 2
        return cmd_verify(args.files, args.outdir, args.time_limit,
                          types=not args.no_types, report=args.report)
    if args.command == "lsp":
        from .lsp import main as lsp_main

        return lsp_main()
    if args.command == "repair":
        return cmd_repair(args.file, args.outdir, args.engine,
                          args.max_iterations, args.time_limit, args.apply,
                          engine_wall=args.engine_wall,
                          engine_effort=_effort(args))
    if args.command == "difftest":
        return cmd_difftest(args.files, args.outdir, args.examples,
                            report=args.report,
                            min_functions=args.min_functions)
    if args.command == "benchmark":
        if args.screen:
            return cmd_screen(args.tasks, time_limit=args.time_limit)
        if args.exam == "proof-repair":
            from .benchmark.exam import render_exam_report, run_repair_exam
            from .repair import make_engine

            try:
                make_engine(args.engine, _wall(args), effort=_effort(args))  # validate the spec up front
            except ValueError as exc:
                print(str(exc), file=sys.stderr)
                return 2
            try:
                scores = run_repair_exam(args.tasks, args.outdir / "exam",
                                         lambda: make_engine(args.engine, _wall(args), effort=_effort(args)),
                                         max_iterations=args.max_iterations,
                                         time_limit=args.time_limit)
            except ValueError as exc:
                print(str(exc), file=sys.stderr)
                return 2
            print(render_exam_report(scores))
            return 0 if scores and all(s.restored for s in scores) else 1
        if args.exam == "spec-writing":
            from .benchmark.specexam import (
                render_spec_exam_report,
                run_spec_exam,
                spec_scores_to_json,
            )
            from .repair import make_engine

            try:
                make_engine(args.engine, _wall(args), effort=_effort(args))  # validate the spec up front
            except ValueError as exc:
                print(str(exc), file=sys.stderr)
                return 2
            ladder = dict(mutant_cap=args.mutant_cap, hunt_timeout=5,
                          dafny_time_limit=args.time_limit,
                          difftest_examples=60)
            if args.quick:
                ladder.update(mutant_cap=min(args.mutant_cap, 3),
                              difftest_examples=20)
            try:
                scores = run_spec_exam(args.tasks, args.outdir / "spec-exam",
                                       lambda: make_engine(args.engine, _wall(args), effort=_effort(args)),
                                       retries=args.retries, **ladder)
            except ValueError as exc:
                print(str(exc), file=sys.stderr)
                return 2
            print(render_spec_exam_report(scores))
            if args.report is not None:
                args.report.parent.mkdir(parents=True, exist_ok=True)
                args.report.write_text(
                    json.dumps(spec_scores_to_json(scores), indent=1))
                print(f"\nreport -> {args.report}")
            # Exit status reports EXAM VALIDITY, never spec quality: a weak
            # spec is a measurement, not a failure.
            return 0 if scores and all(s.valid for s in scores) else 1
        return cmd_benchmark(args.tasks, args.outdir, args.report, args.mutant_cap, args.quick)
    if args.command == "experiment":
        from .benchmark.experiment import (
            exam_roster,
            matrix_rows,
            run_experiment,
            summarize_ledger,
        )

        if args.summarize is not None:
            if not args.summarize.exists():
                print(f"no ledger at {args.summarize}", file=sys.stderr)
                return 2
            print(summarize_ledger(args.summarize))
            return 0
        ledger = args.ledger or (args.outdir / "ledger.jsonl")
        arms = args.arms
        if args.exam == "spec-writing" and arms == ["full", "one-shot"]:
            arms = ["one-shot"]  # the default is proof-repair's; don't error
        try:
            written = run_experiment(
                args.tasks, args.outdir / "cells", args.engines, arms,
                args.trials, ledger, max_iterations=args.max_iterations,
                time_limit=args.time_limit,
                engine_wall=args.engine_wall,
                only_tasks=set(args.only_tasks) if args.only_tasks else None,
                resume=not args.no_resume, exam=args.exam,
                retries=args.retries, engine_effort=_effort(args),
                ladder=dict(mutant_cap=args.mutant_cap, hunt_timeout=5,
                            dafny_time_limit=args.time_limit,
                            difftest_examples=60),
                progress=print)
        except ValueError as exc:
            print(str(exc), file=sys.stderr)
            return 2
        # Exit status covers the WHOLE requested matrix, read back from the
        # ledger — not just the rows this invocation wrote. On resume the
        # completed cells are skipped and never re-emitted, so judging by
        # `written` would report success while the ledger still holds
        # failed trials from an earlier run.
        # Scope to the roster this run actually covered. A ledger is
        # append-only and outlives corpus changes, so a task since renamed
        # or removed keeps its old rows — and an unsuccessful one would
        # fail a matrix that no longer contains it.
        covered = set(args.only_tasks) if args.only_tasks \
            else set(exam_roster(args.tasks, args.exam))
        matrix = matrix_rows(ledger, exam=args.exam, engines=args.engines,
                             arms=arms, trials=args.trials, tasks=covered)
        resumed = len(matrix) - len(written)
        print(f"\n{len(written)} cell-task row(s) appended -> {ledger}"
              + (f" ({resumed} resumed from earlier runs)" if resumed > 0 else "")
              + "\n")
        print(summarize_ledger(ledger))
        if not matrix:
            print("no trials recorded for the requested matrix",
                  file=sys.stderr)
            return 2
        failed = [r for r in matrix if not r["restored"]]
        if failed:
            print(f"\n{len(failed)}/{len(matrix)} trial(s) in this matrix did "
                  f"not succeed", file=sys.stderr)
            return 1
        return 0
    if args.command == "survey":
        return cmd_survey(args.paths, args.top, args.json)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
