"""Translation validation (ARCHITECTURE §6): differential testing of the
encoder, per program.

The loop: annotated Python -> Dafny stub (`encode_module`) -> executable
Python again (`dafny translate py`) -> Hypothesis feeds both the ORIGINAL
function and the Dafny-COMPILED model inputs derived from the typed
signature (filtered by executable `#@ requires`), and compares results
across the value adapter. Any disagreement is an encoder bug by definition
— this is what catches the class of miscompilation the adversarial review
found by hand (division semantics, index normalization, ordering).

The value adapter (CPython list/str/int/bool <-> Dafny runtime Seq/
CodePoint/int/bool) is itself a precise, testable spec of the type
encoding. Verification status is irrelevant here: an unproven-but-encodable
function (e.g. gcd awaiting its lemma pack) still diff-tests.
"""

from __future__ import annotations

import ast
import builtins as _builtins
import copy
import importlib
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

from ..backends.dafny.driver import find_dafny
from ..backends.dafny.encoder import EncodeError, encode_module, load_proof_sidecar
from ..frontend.extract import parse_source
from ..frontend.parse import SAFE_BUILTINS

SAFE_ENV = {
    name: getattr(_builtins, name)
    for name in SAFE_BUILTINS
    if hasattr(_builtins, name)
}

# -- type descriptors ('int' | 'bool' | 'str' | ('list', inner) | ('tuple', ...)) --------------


def type_descriptor(ann: ast.expr | None):
    match ann:
        case ast.Name(id=("int" | "bool" | "str") as n):
            return n
        case ast.Subscript(value=ast.Name(id="list"), slice=inner):
            return ("list", type_descriptor(inner))
        case ast.Subscript(value=ast.Name(id=("tuple" | "Tuple")), slice=sl):
            elts = sl.elts if isinstance(sl, ast.Tuple) else [sl]
            return ("tuple", *(type_descriptor(e) for e in elts))
        case _:
            raise ValueError(f"unsupported annotation: {ast.unparse(ann) if ann else None}")


def strategy_for(tdesc):
    from hypothesis import strategies as st

    match tdesc:
        case "int":
            return st.integers(min_value=-(10 ** 6), max_value=10 ** 6)
        case "bool":
            return st.booleans()
        case "str":
            return st.text(max_size=12)
        case ("list", inner):
            return st.lists(strategy_for(inner), max_size=12)
        case ("tuple", *inners):
            return st.tuples(*(strategy_for(t) for t in inners))
    raise ValueError(f"no strategy for {tdesc!r}")


def to_dafny(value, tdesc):
    import _dafny

    match tdesc:
        case "int" | "bool":
            return value
        case "str":
            return _dafny.Seq(map(_dafny.CodePoint, value))
        case ("list", inner):
            return _dafny.Seq(to_dafny(v, inner) for v in value)
        case ("tuple", *inners):
            return tuple(to_dafny(v, t) for v, t in zip(value, inners))
    raise ValueError(f"cannot adapt {tdesc!r}")


def from_dafny(value, tdesc):
    match tdesc:
        case "int":
            return int(value)
        case "bool":
            return bool(value)
        case "str":
            return "".join(str(cp) for cp in value)
        case ("list", inner):
            return [from_dafny(v, inner) for v in value]
        case ("tuple", *inners):
            return tuple(from_dafny(v, t) for v, t in zip(value, inners))
    raise ValueError(f"cannot adapt {tdesc!r}")


# -- results --------------------------------------------------------------------


@dataclass
class Mismatch:
    args: tuple
    python_result: object
    dafny_result: object


@dataclass
class FunctionDiff:
    name: str
    examples: int
    mismatch: Mismatch | None = None
    error: str | None = None

    @property
    def ok(self) -> bool:
        return self.mismatch is None and self.error is None


@dataclass
class DiffResult:
    path: str
    functions: list[FunctionDiff] = field(default_factory=list)
    error: str | None = None

    @property
    def ok(self) -> bool:
        return self.error is None and all(f.ok for f in self.functions)


# -- core comparison loop ----------------------------------------------------------


def diff_functions(
    original_fn,
    compiled_fn,
    param_names: list[str],
    param_tdescs: list,
    ret_tdesc,
    requires_sources: list[str],
    examples: int,
    kwonly_names: frozenset[str] = frozenset(),
) -> FunctionDiff:
    from hypothesis import HealthCheck, assume, given, settings
    from hypothesis import strategies as st

    requires_codes = [compile(src, "<requires>", "eval") for src in requires_sources]
    captured: dict = {}

    @settings(
        max_examples=examples,
        deadline=None,
        database=None,
        suppress_health_check=list(HealthCheck),
    )
    @given(st.tuples(*(strategy_for(t) for t in param_tdescs)))
    def check(args):
        env = dict(zip(param_names, args))
        for code in requires_codes:
            try:
                ok = bool(eval(code, {"__builtins__": {}}, {**SAFE_ENV, **env}))
            except Exception:
                ok = False
            assume(ok)
        # Keyword-only parameters must be passed by name to the ORIGINAL
        # (the compiled Dafny method takes everything positionally).
        fresh = copy.deepcopy(list(args))
        positional = [v for n, v in zip(param_names, fresh) if n not in kwonly_names]
        keywords = {n: v for n, v in zip(param_names, fresh) if n in kwonly_names}
        expected = original_fn(*positional, **keywords)
        dafny_args = [to_dafny(a, t) for a, t in zip(args, param_tdescs)]
        got = from_dafny(compiled_fn(*dafny_args), ret_tdesc)
        if expected != got:
            captured["m"] = Mismatch(args=args, python_result=expected, dafny_result=got)
            raise AssertionError("divergence")

    try:
        check()
    except AssertionError:
        return FunctionDiff(name=getattr(original_fn, "__name__", "?"), examples=examples,
                            mismatch=captured.get("m"))
    except Exception as exc:  # strategy/adapter/runtime trouble, not divergence
        return FunctionDiff(name=getattr(original_fn, "__name__", "?"), examples=examples,
                            error=f"{type(exc).__name__}: {exc}")
    return FunctionDiff(name=getattr(original_fn, "__name__", "?"), examples=examples)


# -- pipeline --------------------------------------------------------------------------


def _load_original_module(path: Path):
    spec = importlib.util.spec_from_file_location(f"_difftest_orig_{path.stem}", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _load_compiled_module(compiled_dir: Path):
    sys.modules.pop("module_", None)
    sys.path.insert(0, str(compiled_dir))
    try:
        module = importlib.import_module("module_")
    finally:
        sys.path.remove(str(compiled_dir))
    return module


def _compiled_member(default_class, name: str):
    mangled = name.replace("_", "__")
    if hasattr(default_class, mangled):
        return getattr(default_class, mangled)
    for member in dir(default_class):
        if member.replace("__", "_") == name:
            return getattr(default_class, member)
    return None


def difftest_file(path: Path, outdir: Path, examples: int = 100) -> DiffResult:
    result = DiffResult(path=str(path))
    dafny = find_dafny()
    if dafny is None:
        result.error = "dafny not found on PATH"
        return result
    try:
        import _dafny  # noqa: F401  (DafnyRuntimePython)
    except ImportError:
        result.error = "DafnyRuntimePython not installed — pip install DafnyRuntimePython"
        return result

    source = path.read_text()
    specs = parse_source(source, filename=str(path))
    if specs.errors or specs.orphans:
        result.error = "spec errors; run `veripy check` first"
        return result
    try:
        sidecar = load_proof_sidecar(path)  # ghost lemmas: compiled away, must typecheck
        encoded = encode_module(
            source, specs, module_name=path.name, proof_lemmas=sidecar.lemmas
        )
    except EncodeError as exc:
        result.error = f"outside the encoder fragment (line {exc.line}): {exc.message}"
        return result

    workdir = outdir / path.stem
    workdir.mkdir(parents=True, exist_ok=True)
    stub = workdir / f"{path.stem}.dfy"
    stub.write_text(encoded.dafny_source + sidecar.text)
    translate_base = workdir / "compiled"
    # --allow-warnings mirrors the verify driver: a style warning (e.g. a
    # triggerless forall in a proof sidecar) must not fail translation —
    # R4 already established the verdict, and ghost code is erased anyway.
    proc = subprocess.run(
        [dafny, "translate", "py", str(stub), "--output", str(translate_base),
         "--no-verify", "--allow-warnings"],
        capture_output=True, text=True, timeout=600,
    )
    compiled_dir = Path(f"{translate_base}-py")
    if proc.returncode != 0 or not compiled_dir.exists():
        result.error = f"dafny translate failed: {(proc.stdout + proc.stderr)[:300]}"
        return result

    original_module = _load_original_module(path)
    compiled_module = _load_compiled_module(compiled_dir)
    tree = ast.parse(source)
    nodes = {n.name: n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)}

    for spec in specs.functions:
        node = nodes[spec.name]
        try:
            param_tdescs = [
                type_descriptor(p.annotation)
                for p in (*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs)
            ]
            ret_tdesc = type_descriptor(node.returns)
        except ValueError as exc:
            result.functions.append(FunctionDiff(spec.name, 0, error=str(exc)))
            continue
        original_fn = getattr(original_module, spec.name)
        compiled_fn = _compiled_member(compiled_module.default__, spec.name)
        if compiled_fn is None:
            result.functions.append(FunctionDiff(spec.name, 0, error="compiled member not found"))
            continue
        requires_sources = [c.desugared for c in spec.by_kind("requires") if c.desugared]
        diff = diff_functions(
            original_fn, compiled_fn,
            [p.arg for p in (*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs)],
            param_tdescs, ret_tdesc, requires_sources, examples,
            kwonly_names=frozenset(p.arg for p in node.args.kwonlyargs),
        )
        diff.name = spec.name
        result.functions.append(diff)
    return result
