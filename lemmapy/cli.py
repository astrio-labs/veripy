"""LemmaPy CLI (M0): `lemmapy check`, `lemmapy emit`, and `lemmapy survey`."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .frontend.conformance import RULES, aggregate, survey_paths
from .frontend.extract import parse_source
from .backends.runtime.emit import emit_checked

_NOT_ENFORCED = ("invariant", "decreases")


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


def cmd_check(paths: list[Path]) -> int:
    total_errors = 0
    for path in paths:
        total_errors += _report(path)
    if total_errors:
        print(f"\n{total_errors} spec error(s).", file=sys.stderr)
        return 1
    return 0


def cmd_emit(paths: list[Path], outdir: Path) -> int:
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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="lemmapy",
        description="Verify annotated production Python (#@ specs). "
                    "M0: runtime contracts + CrossHair counterexamples.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_check = sub.add_parser("check", help="parse #@ specs and report diagnostics")
    p_check.add_argument("files", nargs="+", type=Path)

    p_emit = sub.add_parser("emit", help="emit icontract-checked copies of modules")
    p_emit.add_argument("files", nargs="+", type=Path)
    p_emit.add_argument("-o", "--outdir", type=Path, default=Path("build/checked"))

    p_survey = sub.add_parser(
        "survey",
        help="read-only fragment-coverage survey over files/directories (M0, RQ1)",
    )
    p_survey.add_argument("paths", nargs="+", type=Path)
    p_survey.add_argument("--top", type=int, default=15)
    p_survey.add_argument("--json", type=Path, default=None)

    args = parser.parse_args(argv)
    if args.command == "check":
        return cmd_check(args.files)
    if args.command == "emit":
        return cmd_emit(args.files, args.outdir)
    if args.command == "survey":
        return cmd_survey(args.paths, args.top, args.json)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
