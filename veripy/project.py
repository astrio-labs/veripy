"""Re-prove enrolled current Python sources and check deterministic proof artifacts."""
from __future__ import annotations
import ast
import hashlib
import io
import json
import os
import re
import tempfile
import tomllib
import tokenize
from pathlib import Path
from veripy.backends.base import get_backend
from veripy.backends.dafny.encoder import EncodeError
from veripy.frontend.extract import parse_source
from veripy.frontend.typegate import _governing_config_dir, _read_config_json, run_type_gate
from veripy.verification.runner import atomic_write_text

class ProjectError(ValueError):
    pass

def _json(value):
    return json.dumps(value, sort_keys=True, indent=2) + "\n"

def _hash(value):
    return hashlib.sha256(value if isinstance(value, bytes) else value.encode()).hexdigest()

def _snapshot(path):
    """Read once; the returned text is exactly what the returned bytes hash.

    Decodes like ``Path.read_text`` so proofs see the same source as before.
    """
    raw = path.read_bytes()
    return raw, io.TextIOWrapper(io.BytesIO(raw)).read()

def _path(root, name, exists=True):
    if not isinstance(name, str) or not name or Path(name).is_absolute():
        raise ProjectError("paths must be nonempty and relative to the manifest")
    path = (root / name).resolve()
    if not path.is_relative_to(root) or (exists and not path.is_file()):
        raise ProjectError(f"missing or escaping project input: {name}")
    return path

def _names(source, specs):
    tree = ast.parse(source)
    names = {}
    def walk(nodes, prefix=""):
        for node in nodes:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                names[node.lineno] = prefix + node.name
                walk(node.body, prefix + node.name + ".<locals>.")
            elif isinstance(node, ast.ClassDef):
                walk(node.body, prefix + node.name + ".")
    walk(tree.body)
    return [names[fn.lineno] for fn in specs.functions]

def _comments(source):
    if not re.search(r"#\s*@", source):
        return []
    return [token.string for token in tokenize.generate_tokens(io.StringIO(source).readline)
            if token.type == tokenize.COMMENT and re.match(r"#\s*@", token.string)]

def _contracts(source, specs, sidecar):
    tree = ast.parse(source)
    annotations = [ast.dump(node.annotation) for node in ast.walk(tree)
                   if isinstance(node, (ast.arg, ast.AnnAssign)) and node.annotation is not None]
    annotations += [ast.dump(node.returns) for node in ast.walk(tree)
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.returns is not None]
    schema = [line.split("# heap-schema:", 1)[1].strip() for line in source.splitlines()
              if line.startswith("# heap-schema:")]
    return {"clauses": [{"function": name, "clauses": [[c.kind, c.raw] for c in fn.clauses]}
                        for name, fn in zip(_names(source, specs), specs.functions)],
            "annotations": annotations, "heap_schema": json.loads("\n".join(schema)) if schema else None,
            "sidecar": sidecar}

def _compiler():
    package = Path(__file__).resolve().parent
    return _hash(_json({p.relative_to(package).as_posix(): _hash(p.read_bytes())
                        for p in sorted(package.rglob("*.py"))}))

def _type_policy(paths, root):
    """Fingerprint the actual governing configs, including inherited policy.

    Configs may live above a manifest directory. Their relative locations are
    metadata, never paths read from a previous lock or executable commands.
    """
    policy = {}
    visited = set()

    def visit(path):
        path = path.resolve()
        if path in visited:
            return  # The existing strict gate diagnoses inheritance cycles.
        visited.add(path)
        policy[Path(os.path.relpath(path, root)).as_posix()] = _hash(path.read_bytes())
        if path.name == "pyproject.toml":
            project = tomllib.loads(path.read_text()).get("tool", {})
            settings = project.get("basedpyright", project.get("pyright", {}))
        else:
            settings = _read_config_json(path)
        if isinstance(settings, dict) and isinstance(settings.get("extends"), str):
            visit(path.parent / settings["extends"])

    for source in paths:
        directory = _governing_config_dir(source)
        if directory is not None:
            config = directory / "pyrightconfig.json"
            visit(config if config.is_file() else directory / "pyproject.toml")
    return policy

def _load(manifest):
    root = manifest.resolve().parent
    manifest_bytes, manifest_text = _snapshot(manifest)
    data = json.loads(manifest_text)
    allowed = {"version", "sources", "required_targets", "targets", "artifacts", "dafny_version"}
    if not isinstance(data, dict) or set(data) != allowed or data["version"] != 1:
        raise ProjectError("manifest requires exactly the documented v1 fields")
    for key in ("sources", "required_targets", "targets"):
        if not isinstance(data[key], list) or not data[key]:
            raise ProjectError(f"{key} must be nonempty")
    required = data["required_targets"]
    if not all(isinstance(x, str) for x in required) or len(set(required)) != len(required):
        raise ProjectError("required target ids must be distinct strings")
    artifacts = _path(root, data["artifacts"], False)
    if artifacts == root or artifacts.is_file():
        raise ProjectError("artifacts must be a dedicated directory")
    targets, seen, inputs = [], set(), {}
    for item in data["targets"]:
        if not isinstance(item, dict) or set(item) - {"id", "source", "backend", "functions", "dependencies", "sidecar"}:
            raise ProjectError("unknown target fields")
        if not {"id", "source", "backend", "functions", "dependencies"} <= set(item):
            raise ProjectError("target is missing required fields")
        name = item["id"]
        if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", name) or name in seen:
            raise ProjectError("target ids must be distinct safe names")
        seen.add(name)
        path = _path(root, item["source"])
        if path.is_relative_to(artifacts):
            raise ProjectError("source cannot be inside generated artifacts")
        # Hash the proved snapshot, not a later read that an editor save
        # could make newer than the source given to the prover.
        # The earliest digest of a path is kept even when another target names
        # this source as a dependency: every proof read happens at or after it,
        # so the final freshness check catches any later save.
        source_bytes, source = _snapshot(path)
        inputs.setdefault(path.relative_to(root).as_posix(), _hash(source_bytes))
        specs = parse_source(source, filename=item["source"])
        if specs.errors or specs.orphans:
            raise ProjectError(f"invalid or orphaned source contracts: {item['source']}")
        functions = item["functions"]
        if not isinstance(functions, list) or not functions or sorted(functions) != sorted(_names(source, specs)):
            raise ProjectError(f"function enrollment mismatch: {item['source']}")
        if item["backend"] not in {"dafny", "dafny-outcomes", "dafny-native", "dafny-heap"}:
            raise ProjectError("project supports the explicitly registered Dafny source backends")
        backend = get_backend(item["backend"])
        sidepath = backend.sidecar_path(path)
        if "sidecar" in item:
            declared = _path(root, item["sidecar"])
            if declared != sidepath:
                raise ProjectError("sidecar must be the source's .proofs.dfy companion")
        elif sidepath.exists():
            raise ProjectError("existing proof sidecar must be explicitly enrolled")
        if not isinstance(item["dependencies"], list):
            raise ProjectError("dependencies must be an explicit list")
        dependencies = [_path(root, p) for p in item["dependencies"]]
        for file in [path, *dependencies, *([sidepath] if sidepath.exists() else [])]:
            # Generated output must never overwrite an enrolled definition or
            # sidecar, including a dependency named like an emitted artifact.
            if file.is_relative_to(artifacts):
                raise ProjectError("project inputs cannot be inside generated artifacts")
            if file != path:
                # Read later by the type gate/prover, so a change after this
                # hash is caught by the final freshness check.
                inputs.setdefault(file.relative_to(root).as_posix(), _hash(file.read_bytes()))
        targets.append((item, path, source, specs, backend))
    if seen != set(required):
        raise ProjectError("required targets and actual enrollment differ")
    discovered = set()
    for pattern in data["sources"]:
        if not isinstance(pattern, str) or Path(pattern).is_absolute() or ".." in Path(pattern).parts:
            raise ProjectError("source globs must stay within the project")
        for path in root.glob(pattern):
            if path.is_file() and path.suffix == ".py" and _comments(path.read_text()):
                _path(root, path.relative_to(root).as_posix())
                discovered.add(path.resolve())
    selected = [target[1] for target in targets]
    if len(set(selected)) != len(selected) or discovered != set(selected):
        raise ProjectError("annotated-source discovery differs from enrollment")
    if not isinstance(data["dafny_version"], str) or not data["dafny_version"]:
        raise ProjectError("an exact Dafny version is required")
    return root, data, artifacts, targets, inputs, manifest_bytes

def _prove(item, path, source, specs, backend, root, temporary, time_limit):
    row = {"id": item["id"], "source": item["source"], "backend": item["backend"],
           "functions": item["functions"], "proof_status": "unsupported", "diagnostics": []}
    try:
        sidecar = backend.load_sidecar(path)
        backend.validate_sidecar(sidecar.text)
        encoded = backend.encode(source, specs, module_name=path.name, proof_lemmas=sidecar.lemmas)
        if not encoded.methods:
            raise ProjectError("backend emitted no source methods")
        generated = backend.encoded_text(encoded)
        combined = backend.compose_artifact(encoded, sidecar)
        artifact = temporary / (item["id"] + ".dfy")
        artifact.write_text(combined)
        extent = getattr(encoded, "artifact_extent", generated.count("\n") + 1)
        result = backend.verify_artifact(artifact, encoded.line_map, time_limit=time_limit, extent=extent)
        row["backend_output"] = result.raw
        row["summary"] = result.summary
        if result.error:
            row["proof_status"] = "timeout" if "timed out" in result.error.lower() else "tool-error"
            row["diagnostics"].append({"file": item["source"], "line": None, "message": result.error})
        else:
            matched = re.search(r"finished with (\d+) verified, (\d+) error", result.summary)
            if result.ok and matched and int(matched[1]) >= len(encoded.methods) and int(matched[2]) == 0:
                row["proof_status"] = "verified"
            elif result.ok:
                row["proof_status"] = "tool-error"
                row["diagnostics"].append({"file": item["source"], "line": None,
                    "message": "prover did not report verification of the emitted source methods"})
            else:
                row["proof_status"] = "timeout" if any(d.obligation == "timeout" for d in result.diagnostics) else "failed"
            for diagnostic in result.diagnostics:
                where = sidecar.locate(diagnostic.dafny_line, extent) if hasattr(sidecar, "locate") else None
                file, line = (Path(where[0]).relative_to(root).as_posix(), where[1]) if where else (item["source"], diagnostic.py_line)
                row["diagnostics"].append({"file": file, "line": line, "message": diagnostic.message,
                                           "kind": diagnostic.obligation, "severity": diagnostic.severity})
            # Prefer the explicit contract location for appended proof obligations.
            for raw in result.raw.splitlines():
                related = re.search(r"\.dfy\((\d+),\d+\): Related location", raw)
                if related and row["diagnostics"] and hasattr(sidecar, "locate"):
                    where = sidecar.locate(int(related[1]), extent)
                    if where:
                        row["diagnostics"][-1].update(file=Path(where[0]).relative_to(root).as_posix(), line=where[1])
        mapping = {"source": item["source"], "functions": item["functions"],
                   "generated_to_source": encoded.line_map,
                   "translation": getattr(encoded, "translation", None)}
        contract = _contracts(source, specs, path.with_suffix(".proofs.dfy").read_text() if sidecar.path and sidecar.path.exists() else "")
        return row, combined, mapping, contract
    except (EncodeError, ValueError, SyntaxError, TypeError, KeyError, IndexError) as error:
        row["diagnostics"].append({"file": item["source"], "line": getattr(error, "line", None), "message": str(error)})
        return row, None, None, None
    except OSError as error:
        row["proof_status"] = "tool-error"
        row["diagnostics"].append({"file": item["source"], "line": None, "message": str(error)})
        return row, None, None, None


def run_project(manifest, mode="check", *, update_enrollment=False, update_contracts=False, time_limit=30):
    """Always re-prove current inputs. Only successful generate writes artifacts."""
    manifest = Path(manifest).resolve()
    report = {"schema": "veripy-project-result/1", "status": "enrollment-error", "targets": []}
    if mode not in {"generate", "check"} or type(time_limit) is not int or time_limit <= 0:
        report["error"] = "invalid mode or proof time limit"
        return report
    try:
        root, data, artifacts, targets, inputs, manifest_bytes = _load(manifest)
        lock_path = artifacts / "project.lock.json"
        previous = json.loads(lock_path.read_text()) if lock_path.exists() else None
        if previous is not None and (not isinstance(previous, dict) or previous.get("schema") != "veripy-project-lock/1"):
            raise ProjectError("invalid project artifact lock")
        enrollment = {"sources": data["sources"], "required_targets": data["required_targets"], "targets": data["targets"]}
        if previous and previous.get("enrollment") != enrollment and not (mode == "generate" and update_enrollment):
            raise ProjectError("enrollment changed; review and generate --update-enrollment explicitly")
        compiler = _compiler()
        type_policy = _type_policy([target[1] for target in targets], root)
        gate = run_type_gate([target[1] for target in targets])
        report["typechecker_version"] = gate.version
        report["type_diagnostics"] = [vars(d) for d in gate.diagnostics]
        if not gate.available or gate.errors:
            report["status"] = "tool-error" if not gate.available else "type-error"
            report["error"] = gate.error
            report["diagnostics"] = [vars(d) for d in gate.errors]
            return report
        versions = {target[4].prover_version() for target in targets}
        if None in versions or len(versions) != 1 or next(iter(versions)).split("+")[0] != data["dafny_version"]:
            report.update(status="tool-error", error="Dafny missing or version differs from manifest")
            return report
        report["dafny_version"] = next(iter(versions))
        outputs, contracts = {}, {}
        with tempfile.TemporaryDirectory(prefix="veripy-project-") as temporary:
            for item, path, source, specs, backend in targets:
                row, combined, mapping, contract = _prove(item, path, source, specs, backend, root, Path(temporary), time_limit)
                report["targets"].append(row)
                if combined is not None:
                    outputs[item["id"] + ".dfy"] = combined
                    outputs[item["id"] + ".map.json"] = _json(mapping)
                    contracts[item["id"]] = contract
        failed = [row for row in report["targets"] if row["proof_status"] != "verified"]
        if failed:
            report["status"] = failed[0]["proof_status"]
            return report
        if (manifest.read_bytes() != manifest_bytes or _compiler() != compiler
                or _type_policy([target[1] for target in targets], root) != type_policy
                or any(_hash(_path(root, name).read_bytes()) != digest for name, digest in inputs.items())):
            report.update(status="stale", error="inputs changed during verification; retry on a stable checkout")
            return report
        lock = {"schema": "veripy-project-lock/1", "enrollment": enrollment, "inputs": inputs,
                "contracts": contracts, "compiler": compiler, "dafny_version": report["dafny_version"],
                "typechecker_version": gate.version,
                "type_policy": type_policy,
                "artifacts": {name: _hash(text) for name, text in outputs.items()}}
        if previous and (previous.get("contracts") != contracts or previous.get("type_policy", {}) != type_policy):
            report["contract_changes"] = {
                "targets": {name: {"before": previous.get("contracts", {}).get(name), "after": contracts.get(name)}
                            for name in sorted(set(previous.get("contracts", {})) | set(contracts))
                            if previous.get("contracts", {}).get(name) != contracts.get(name)},
                "type_policy": {"before": previous.get("type_policy", {}), "after": type_policy},
            }
            if mode == "generate" and not update_contracts:
                report.update(status="contract-change", error="contract, proof assumptions or type policy changed; review and generate --update-contracts explicitly")
                return report
        outputs["project.lock.json"] = _json(lock)
        if mode == "check":
            stale = [name for name, text in outputs.items() if not (artifacts / name).is_file() or (artifacts / name).read_text() != text]
            report["status"] = "stale" if stale else "verified"
            report["stale_artifacts"] = stale
        else:
            artifacts.mkdir(parents=True, exist_ok=True)
            for name, text in outputs.items():
                atomic_write_text(artifacts / name, text)
            report["status"] = "verified"
        report["artifacts"] = data["artifacts"]
        return report
    except (ProjectError, OSError, ValueError, SyntaxError, TypeError, KeyError, tokenize.TokenError) as error:
        report["error"] = str(error)
        return report
