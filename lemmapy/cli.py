"""LemmaPy CLI (M0): `lemmapy check`, `lemmapy emit`, and `lemmapy survey`."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

from .frontend.conformance import RULES, aggregate, survey_paths
from .frontend.extract import parse_source
from .frontend.typegate import run_type_gate
from .backends.dafny.driver import verify_dafny_file
from .backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar
from .backends.runtime.emit import emit_checked

_NOT_ENFORCED = ("invariant", "decreases", "proof")


def _report(path: Path) -> int:
    """Print a per-function spec report; return the number of errors."""
    specs = parse_source(path.read_text(), filename=str(path))
    errors = 0
    print(f"{path}")
    if not specs.functions and not specs.orphans:
        print("  (no #@ specs found)")
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
            print(f"{path}: spec errors; run `lemmapy check` first", file=sys.stderr)
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
            "hunt: crosshair not found — install with `pip install 'lemmapy[dev]'`",
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
    from .report import build_report, function_report, render_report_text

    outdir.mkdir(parents=True, exist_ok=True)
    failed = 0
    trouble = 0
    fn_reports: list = []
    sidecar_lemmas: dict[str, list[str]] = {}
    dafny_version: str | None = None
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
            print(f"{path}: spec errors; run `lemmapy check` first", file=sys.stderr)
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
        stub = outdir / f"{path.stem}.dfy"
        stub.write_text(encoded.dafny_source + sidecar.text)
        result = verify_dafny_file(stub, encoded.line_map, time_limit=time_limit)
        if result.error is not None:
            print(f"{path}: dafny trouble: {result.error}", file=sys.stderr)
            trouble += 1
            fn_reports += [function_report(fn, str(path), "error") for fn in specs.functions]
            continue
        dafny_version = dafny_version or result.summary or "ran"
        if result.ok:
            print(f"{path}: VERIFIED ({', '.join(encoded.methods)}) -> {stub}")
            fn_reports += [function_report(fn, str(path), "verified") for fn in specs.functions]
        else:
            failed += 1
            print(f"{path}: VERIFICATION FAILED -> {stub}")
            errs = []
            stub_extent = encoded.dafny_source.count("\n") + 1
            for d in result.diagnostics:
                if d.severity == "error":
                    where = f"{path}:{d.py_line}" if d.py_line is not None else f"{stub}:{d.dafny_line}"
                    print(f"  {where}: {d.message}")
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
                    fails = [{"file": str(stub), "line": d.dafny_line,
                              "message": f"unattributed (proof sidecar or "
                                         f"generated region): {d.message}"}
                             for d in unattributed]
                else:
                    status_str = "failed" if mine else "verified"
                fn_reports.append(function_report(fn, str(path), status_str, fails))
    if report is not None:
        payload = build_report(fn_reports, sidecar_lemmas, dafny_version)
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text(json.dumps(payload, indent=1))
        print(f"\n{render_report_text(payload)}")
        print(f"\nreport -> {report}")
    if trouble:
        return 2
    return 1 if failed else 0


def cmd_difftest(paths: list[Path], outdir: Path, examples: int) -> int:
    """Translation validation (§6): original Python vs Dafny-compiled model."""
    from .difftest.harness import difftest_file

    diverged = 0
    trouble = 0
    for path in paths:
        result = difftest_file(path, outdir, examples=examples)
        if result.error:
            print(f"{path}: difftest trouble: {result.error}", file=sys.stderr)
            trouble += 1
            continue
        for fn in result.functions:
            if fn.ok:
                print(f"{path}::{fn.name}: OK ({fn.examples} examples)")
            elif fn.mismatch is not None:
                diverged += 1
                m = fn.mismatch
                print(f"{path}::{fn.name}: DIVERGENCE (encoder bug)")
                print(f"  args={m.args!r}")
                print(f"  python={m.python_result!r}  dafny-model={m.dafny_result!r}")
            else:
                trouble += 1
                print(f"{path}::{fn.name}: trouble: {fn.error}", file=sys.stderr)
    if diverged:
        return 1
    return 2 if trouble else 0


def cmd_benchmark(tasks: Path, outdir: Path, report: Path | None,
                 mutant_cap: int, quick: bool) -> int:
    from .benchmark.runner import ERROR, FAIL, render_report, run_benchmark, scores_to_json

    kwargs = dict(mutant_cap=mutant_cap, hunt_timeout=5,
                  dafny_time_limit=60, difftest_examples=60)
    if quick:
        kwargs.update(mutant_cap=min(mutant_cap, 3), difftest_examples=20)
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
                f"spec; proof status comes from `lemmapy verify`): "
                f"{', '.join(unmarked)}"
            )
    return status


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="lemmapy",
        description="Verify annotated production Python (#@ specs). "
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
             "state) — the agent interface consumed by `lemmapy repair`",
    )
    p_verify.add_argument(
        "--hunt-counterexamples", action="store_true",
        help="with --json: run CrossHair on failing modules to attach a "
             "concrete counterexample when one exists",
    )

    p_difftest = sub.add_parser(
        "difftest",
        help="differentially test original Python vs the Dafny-compiled model (§6)",
    )
    p_difftest.add_argument("files", nargs="+", type=Path)
    p_difftest.add_argument("-o", "--outdir", type=Path, default=Path("build/difftest"))
    p_difftest.add_argument("-n", "--examples", type=int, default=100)

    p_benchmark = sub.add_parser(
        "benchmark",
        help="run lemmapy-benchmark: assurance-ladder scoring over annotated-Python tasks",
    )
    p_benchmark.add_argument("--tasks", type=Path, default=Path("benchmark/tasks"))
    p_benchmark.add_argument("-o", "--outdir", type=Path, default=Path("build/benchmark"))
    p_benchmark.add_argument("--report", type=Path, default=None)
    p_benchmark.add_argument("--mutant-cap", type=int, default=8)
    p_benchmark.add_argument("--quick", action="store_true",
                            help="small mutant panels and example counts (CI mode)")

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
                    payloads = [
                        {"schema": "lemmapy-failures/1", "file": f,
                         "status": "gate-error", "functions": [],
                         "failures": fails or (
                             [] if gate.available else
                             [{"kind": "type", "py_line": None,
                               "message": f"type gate unavailable: {gate.error}"}]),
                         "sidecar": None}
                        for f, fails in by_file.items()
                    ]
                    try:
                        dump(payloads, args.json_out)
                    except OSError as exc:
                        print(f"cannot write {args.json_out}: {exc}", file=sys.stderr)
                        return 2
                    print("type gate failed; structured payloads written to "
                          f"{args.json_out}; fix types or pass --no-types",
                          file=sys.stderr)
                    return 2
            payloads = verify_structured_many(
                args.files, args.outdir, time_limit=args.time_limit,
                hunt_counterexamples=args.hunt_counterexamples)
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
        return cmd_verify(args.files, args.outdir, args.time_limit,
                          types=not args.no_types, report=args.report)
    if args.command == "difftest":
        return cmd_difftest(args.files, args.outdir, args.examples)
    if args.command == "benchmark":
        return cmd_benchmark(args.tasks, args.outdir, args.report, args.mutant_cap, args.quick)
    if args.command == "survey":
        return cmd_survey(args.paths, args.top, args.json)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
