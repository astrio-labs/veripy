"""Check retained inputs and optionally regenerate every paired proof artifact."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT.parent))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--encode", action="store_true", help="Check admission and sidecar composition without invoking provers")
    args = parser.parse_args()
    origins = json.loads((ROOT / "origins.json").read_text())
    for name, record in origins.items():
        path = ROOT / name
        assert hashlib.sha256(path.read_bytes()).hexdigest() == record["sha256"], name
    components = json.loads((ROOT / "components.json").read_text())
    assert len(components) == len({row["component"] for row in components}) == 25
    encoded = []
    for row in components:
        assert row["lean_source"] == row["dafny_source"]
        source = ROOT.parent / row["lean_source"]
        assert source.is_file(), source
        if args.encode:
            from veripy.backends.base import get_backend
            from veripy.frontend.extract import parse_source
            text = source.read_text()
            specs = parse_source(text, filename=str(source))
            assert not specs.errors and not specs.orphans, row["component"]
            for backend in ("lean", row["dafny_backend"]):
                engine = get_backend(backend)
                sidecar = engine.load_sidecar(source)
                model = engine.encode(text, specs, module_name=source.name, proof_lemmas=sidecar.lemmas)
                artifact = engine.compose_artifact(model, sidecar)
                assert artifact.strip()
                encoded.append({"component": row["component"], "backend": backend})
    comparisons = json.loads((ROOT / "compatibility.json").read_text())
    assert len(comparisons) == len({row["id"] for row in comparisons}) == 10
    for row in comparisons:
        for version in ("old", "new"):
            path = ROOT.parent / row[version]
            assert hashlib.sha256(path.read_bytes()).hexdigest() == row[version + "_sha256"]
        if row.get("relation"):
            assert (ROOT.parent / row["relation"]).is_file()
    print(json.dumps({"status": "passed", "bound_files": len(origins), "paired_units": len(components), "historical_comparisons": len(comparisons), "encodings": encoded, "note": "Hashes and successful encoding are not fresh proof results."}, indent=2))


if __name__ == "__main__":
    main()
