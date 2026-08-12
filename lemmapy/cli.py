"""LemmaPy CLI (M0): `lemmapy check` and `lemmapy emit`."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

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

    args = parser.parse_args(argv)
    if args.command == "check":
        return cmd_check(args.files)
    if args.command == "emit":
        return cmd_emit(args.files, args.outdir)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
