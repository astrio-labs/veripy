"""Recheck retained comparison inputs with the current compiler in a fresh directory."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT.parent))
from veripy.compatibility import compare


def native_witness(row, out):
    modules = []
    for version in ("old", "new"):
        source = ROOT.parent / row[version]
        namespace = {}
        exec(compile(source.read_text(), str(source), "exec"), namespace)
        modules.append(namespace)
    observed = []
    for case in row["witnesses"]:
        outcomes = []
        for module in modules:
            try:
                value = module[row["function"]](**case["arguments"])
                outcomes.append({"return": value})
            except ValueError as exc:
                outcomes.append({"exception": type(exc).__name__})
        observed.append({"arguments": case["arguments"], "old": outcomes[0], "new": outcomes[1]})
    result = {"status": "counterexample-found" if any(r["old"] != r["new"] for r in observed) else "inconclusive", "witnesses": observed, "matches_recorded_witnesses": observed == row["witnesses"]}
    out.mkdir()
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--projects", nargs="+")
    parser.add_argument("--wall", type=int, default=60)
    args = parser.parse_args()
    rows = json.loads((ROOT / "compatibility.json").read_text())
    if args.wall <= 0:
        parser.error("--wall must be positive")
    if args.projects:
        unknown = set(args.projects) - {r["id"] for r in rows}
        if unknown:
            parser.error(f"Unknown projects: {sorted(unknown)}")
        rows = [r for r in rows if r["id"] in args.projects]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    results = []
    for row in rows:
        for version in ("old", "new"):
            path = ROOT.parent / row[version]
            assert hashlib.sha256(path.read_bytes()).hexdigest() == row[version + "_sha256"], path
        if row["mode"] == "native-witness":
            result = native_witness(row, out / row["id"])
        else:
            result = compare(ROOT.parent / row["old"], ROOT.parent / row["new"], out / row["id"], old_function=row["function"], backend=row["backend"], time_limit=args.wall, relation=ROOT.parent / row["relation"] if row.get("relation") else None)
        results.append({"id": row["id"], "recorded_status": row["recorded_status"], "current_status": result["status"], "matches_recorded": result["status"] == row["recorded_status"] and result.get("matches_recorded_witnesses", True), "result": f"{row['id']}/result.json"})
        (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(row["id"], result["status"], flush=True)
    # Inconclusive and unsupported are legitimate recorded outcomes. Surface drift.
    return 0 if all(r["matches_recorded"] for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
