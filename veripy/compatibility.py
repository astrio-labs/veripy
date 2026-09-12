"""Prove backward compatibility of two annotated, closed Python functions.

The product checks old-pre => new-pre, equal ValueError outcomes, and equal
normal returns. It verifies both bodies and every sidecar in the same artifact.
Proof failure is inconclusive unless bounded native replay supplies a witness.
"""
from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys

from .backends.base import get_backend
from .backends.dafny.encoder import EncodeError
from .frontend.extract import parse_source
from .frontend.records import record_schemas, RecordError
from .backends.dafny.environment import resolve_for_encoder


def _type(node):
    if isinstance(node, ast.Name) and node.id in {'int', 'bool', 'str'}:
        return node.id
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
        if node.value.id == 'list':
            return ('list', _type(node.slice))
        if node.value.id == 'tuple' and isinstance(node.slice, ast.Tuple):
            return ('tuple', *(_type(n) for n in node.slice.elts))
    raise ValueError('comparison boundaries support int, bool, str, lists and fixed tuples only')


def _signature(source, name):
    environment = resolve_for_encoder(ast.parse(source))
    tree = environment.module
    # The comparison observes a closed module, not a selected definition that
    # could be replaced by later top-level execution.
    records = record_schemas(tree)
    if any(d['resolution'] != 'encoder-model' for d in environment.dependencies):
        raise ValueError('comparison requires explicit modeled dependencies; unresolved import')
    for node in tree.body:
        allowed = (isinstance(node, ast.FunctionDef)
                   or isinstance(node, ast.ClassDef) and node.name in records
                   or isinstance(node, (ast.Import, ast.ImportFrom))
                   or isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
                   and isinstance(node.value.value, str))
        if not allowed:
            raise ValueError('comparison requires a closed module with supported imports/records only')
    fn = next((n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name), None)
    if fn is None:
        raise ValueError(f'missing function {name}')
    a = fn.args
    if a.vararg or a.kwarg or fn.decorator_list:
        raise ValueError('comparison requires undecorated parameters without variadics')
    defaults = [*a.defaults, *[d for d in a.kw_defaults if d is not None]]
    if any(not isinstance(d, ast.Constant) or type(d.value) not in (int, bool, str, type(None)) for d in defaults):
        raise ValueError('comparison defaults require immutable scalar literals')
    positional = [*a.posonlyargs, *a.args]
    bindings = list(zip(positional[len(positional)-len(a.defaults):], a.defaults))
    bindings += [(p,d) for p,d in zip(a.kwonlyargs,a.kw_defaults) if d is not None]
    if any(_type(p.annotation) != type(d.value).__name__ for p,d in bindings):
        raise ValueError('comparison default must inhabit the exact admitted parameter type')
    parameters = [(p.arg, _type(p.annotation), kind) for group, kind in
                  ((a.posonlyargs, 'positional-only'), (a.args, 'positional-or-keyword'),
                   (a.kwonlyargs, 'keyword-only')) for p in group]
    # Equal signatures include exact default ASTs (True must not equal 1).
    # Equal admitted argument values then cover every shared omission pattern.
    default_signature = ([ast.dump(d) for d in a.defaults],
                         [ast.dump(d) if d is not None else None for d in a.kw_defaults])
    return parameters, _type(fn.returns), default_signature


def _header(text, name):
    match = re.search(r'^method (?:\{:[^\n]*?\} )?' + re.escape(name) + r'\(([^\n]*)\) returns \(([^\n]*)\)\n(.*?)^\{', text, re.M | re.S)
    if not match:
        raise ValueError('cannot locate encoded entry point')
    params, returns, clauses = match.groups()
    # The header must be one line; do not silently absorb another method.
    if '\n' in params or '\n' in returns:
        raise ValueError('unsupported encoded method header')
    requires = [line.strip()[9:] for line in clauses.splitlines() if line.strip().startswith('requires ')]
    return params, returns, requires


def _samples(typ):
    if typ == 'int':
        return [-2, -1, 0, 1, 2, 35, 36, 37, 1295, 1296, 1297]
    if typ == 'bool':
        return [False, True]
    if typ == 'str':
        return ['', 'a', '0', 'hello', '\u0660']
    if typ[0] == 'list':
        values = _samples(typ[1])
        return [[], *[[v] for v in values[:5]], values[:3], list(reversed(values[:3]))]
    return list(itertools.islice(itertools.product(*(_samples(t) for t in typ[1:])), 100))


def _replay(paths, names, signature):
    functions, pres = [], []
    for path, name in zip(paths, names):
        source = Path(path).read_text()
        tree = ast.parse(source)
        # Encoding admits some declarative top-level syntax. Native replay is
        # deliberately narrower and never executes imports or decorators.
        if any(not isinstance(n, ast.FunctionDef) for n in tree.body):
            return {'reason': 'native replay requires function-only modules'}
        _signature(source, name)  # validate literal defaults before executing definitions
        ns = {}
        exec(compile(tree, str(path), 'exec'), ns)
        functions.append(ns[name])
        spec = next(f for f in parse_source(source).functions if f.name == name)
        pres.append([compile(c.desugared, '<requires>', 'eval') for c in spec.by_kind('requires')])
    admitted = 0
    for args in itertools.islice(itertools.product(*(_samples(p[1]) for p in signature)), 1000):
        env = dict(zip((p[0] for p in signature), args))
        try:
            accepts = [all(eval(c, {}, env) for c in cs) for cs in pres]
        except Exception:
            continue
        if not accepts[0]:
            continue
        admitted += 1
        if not accepts[1]:
            return {'admitted_samples': admitted, 'witness': {'arguments': args, 'kind': 'precondition-narrowing'}}
        results = []
        for fn in functions:
            try:
                values = copy.deepcopy(args)
                positional = [v for p,v in zip(signature,values) if p[2] != 'keyword-only']
                keywords = {p[0]:v for p,v in zip(signature,values) if p[2] == 'keyword-only'}
                results.append({'return': fn(*positional, **keywords)})
            except Exception as exc:
                results.append({'exception': type(exc).__module__ + '.' + type(exc).__qualname__})
        if results[0] != results[1]:
            return {'admitted_samples': admitted, 'witness': {'arguments': args, 'old': results[0], 'new': results[1], 'kind': 'observable-difference'}}
    return {'admitted_samples': admitted, 'reason': 'bounded replay found no difference; this is not a proof'}


def compare(old: Path | str, new: Path | str, out: Path | str, *, old_function='f', new_function=None,
            backend='dafny', time_limit=20, relation: Path | str | None = None):
    """Return and persist a four-way verdict. ``out`` must be a fresh directory.

    Optional relation is a checked sidecar defining CompatibilityRelation with
    the entry parameters. Its requirements must hold at the product call site.
    It can relate differently named mathematical specifications across modules.
    """
    paths = [Path(old).resolve(), Path(new).resolve()]
    names = [old_function, new_function or old_function]
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    report = {'status': 'inconclusive', 'backend': backend, 'functions': names,
              'scope': 'typed value equality and modeled exception class under stable explicit dependencies; equal literal defaults and parameter kinds include omitted arguments; excludes exception messages, identity, resources and whole-repository compatibility',
              'inputs': {}, 'proof': {}}
    try:
        if time_limit <= 0:
            raise ValueError('time_limit must be positive')
        if backend not in {'dafny', 'dafny-outcomes'}:
            raise ValueError('comparison supports dafny and dafny-outcomes only')
        engine = get_backend(backend)
        sources = [p.read_text() for p in paths]
        signatures = [_signature(s, n) for s, n in zip(sources, names)]
        if signatures[0] != signatures[1]:
            raise ValueError('parameter names, kinds, types, literal defaults and return types must match')
        environments = [resolve_for_encoder(ast.parse(s)) for s in sources]
        if environments[0].exceptions != environments[1].exceptions:
            raise ValueError('comparison requires matching modeled exception names and hierarchy')
        report['environments'] = [{'constants': e.values, 'dependencies': e.dependencies,
                                   'newtypes': e.newtypes, 'exceptions': e.exceptions,
                                   'regex_models': sorted(e.regex_models)} for e in environments]
        report['signature'] = signatures[0]
        modules, calls, headers, replay_paths = [], [], [], []
        for index, (path, source, name) in enumerate(zip(paths, sources, names)):
            label = ('Old', 'New')[index]
            specs = parse_source(source, filename=str(path))
            if specs.errors or specs.orphans or len(specs.functions) != sum(isinstance(n, ast.FunctionDef) for n in ast.parse(source).body):
                raise ValueError('invalid or orphaned annotations')
            frozen = out / (label.lower() + '.py')
            frozen.write_text(source)
            report['inputs'][str(path)] = hashlib.sha256(source.encode()).hexdigest()
            proof_path = engine.sidecar_path(path)
            if proof_path.exists():
                proof_bytes = proof_path.read_bytes()
                engine.sidecar_path(frozen).write_bytes(proof_bytes)
                report['inputs'][str(proof_path)] = hashlib.sha256(proof_bytes).hexdigest()
            replay_paths.append(str(frozen))
            sidecar = engine.load_sidecar(frozen)
            encoded = engine.encode(source, specs, module_name=path.name, proof_lemmas=sidecar.lemmas)
            artifact = engine.compose_artifact(encoded, sidecar)
            entry = encoded.method_names[name]
            params, returns, requires = _header(engine.encoded_text(encoded), entry)
            if 'VeriPyCompatibilityAdmitted' in artifact:
                raise ValueError('reserved comparison symbol')
            admission = ' && '.join('(' + r + ')' for r in requires) or 'true'
            modules.append(f'module {label}Version {{\n{artifact}\npredicate VeriPyCompatibilityAdmitted({params}) {{ {admission} }}\n}}\n')
            calls.append(f'{label}.{entry}')
            headers.append((params, returns))
        if headers[0][0] != headers[1][0]:
            raise ValueError('encoded parameter representations differ')
        params = headers[0][0]
        # Tuple types contain commas: take argument names from the actual
        # generated bindings, rather than splitting their type expressions.
        parameter_names = re.findall(r'(?:^|, )([A-Za-z_][A-Za-z_0-9]*): ', params)
        if set(parameter_names) & {'Old', 'New', 'CompatibilityRelation', 'BackwardCompatible'}:
            raise ValueError('parameter collides with a comparison namespace or relation symbol')
        args = ', '.join(parameter_names)
        used = set(parameter_names)
        def fresh(base):
            while base in used:
                base += '_'
            used.add(base)
            return base
        old_value, new_value, old_error, new_error = map(fresh, ('oldResult', 'newResult', 'oldError', 'newError'))
        text = ''.join(modules) + '\nimport Old = OldVersion\nimport New = NewVersion\n'
        hint = ''
        if relation is not None:
            relation = Path(relation).resolve()
            proof = relation.read_text()
            engine.validate_sidecar(proof)
            report['inputs'][str(relation)] = hashlib.sha256(proof.encode()).hexdigest()
            (out / 'relation.dfy').write_text(proof)
            text += '\n' + proof + '\n'
            hint = f'  CompatibilityRelation({args});\n'
        outcomes = [len(re.findall(r'(?:^|, )([A-Za-z_][A-Za-z_0-9]*): ', header[1])) == 2 for header in headers]
        tagged = backend == 'dafny-outcomes' and bool(environments[0].exceptions)
        # The outcome backend assigns the same sorted-name tags when the
        # independently resolved class hierarchies match above.
        if any(outcomes) and tagged and not all(outcomes):
            raise ValueError('inconsistent tagged outcome representations')
        text += f'''\nmethod BackwardCompatible({params})
  requires Old.VeriPyCompatibilityAdmitted({args})
{{
{hint}  assert New.VeriPyCompatibilityAdmitted({args});
  var {old_value}{', '+old_error if outcomes[0] else ''} := {calls[0]}({args});
  var {new_value}{', '+new_error if outcomes[1] else ''} := {calls[1]}({args});
'''
        if not outcomes[0]:
            text += f'  var {old_error} := false;\n'
        if not outcomes[1]:
            text += f'  var {new_error} := false;\n'
        normal = f'{old_error} == 0' if tagged else f'!{old_error}'
        text += f'  assert {old_error} == {new_error};\n  if {normal} {{ assert {old_value} == {new_value}; }}\n'
        text += '}\n'
        target = out / 'comparison.dfy'
        target.write_text(text)
        result = engine.verify_artifact(target, {}, time_limit=time_limit, extent=None)
        (out / 'proof.log').write_text(result.raw + (result.error or ''))
        report['proof'] = {'ok': result.ok, 'summary': result.summary, 'error': result.error,
                           'artifact_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                           'prover': engine.prover_version()}
        if result.ok:
            report.update(status='proved-compatible', reason='Both bodies, all sidecars, input admission and observable equality verified together.')
        else:
            report['reason'] = 'Product proof failed or exceeded budget; proof failure is not a behavioral difference.'
        request = out / 'replay-request.json'
        request.write_text(json.dumps({'paths': replay_paths, 'names': names, 'signature': signatures[0][0]}))
        try:
            replay = subprocess.run([sys.executable, '-m', 'veripy.compatibility', '--replay', str(request)], capture_output=True, text=True, timeout=10)
            report['replay'] = json.loads(replay.stdout) if replay.returncode == 0 else {'reason': 'native replay unavailable'}
        except (subprocess.TimeoutExpired, ValueError):
            report['replay'] = {'reason': 'native replay exceeded budget or returned invalid output'}
        if 'witness' in report['replay']:
            # A contradiction invalidates a proof claim and remains conspicuous.
            report['proof_replay_contradiction'] = result.ok
            report.update(status='behavioral-difference', witness=report['replay']['witness'])
    except (EncodeError, RecordError, ValueError, SyntaxError, OSError, KeyError) as exc:
        report.update(status='unsupported', reason=str(exc))
    (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', type=Path, help=argparse.SUPPRESS)
    parser.add_argument('--old', type=Path)
    parser.add_argument('--new', type=Path)
    parser.add_argument('--function', default='f')
    parser.add_argument('--new-function')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--backend', choices=['dafny', 'dafny-outcomes'], default='dafny')
    parser.add_argument('--time-limit', type=int, default=20)
    parser.add_argument('--relation', type=Path)
    args = parser.parse_args()
    if args.replay:
        print(json.dumps(_replay(**json.loads(args.replay.read_text()))))
        return
    if not (args.old and args.new and args.out):
        parser.error('--old, --new and --out are required')
    print(json.dumps(compare(args.old, args.new, args.out, old_function=args.function,
                            new_function=args.new_function, backend=args.backend,
                            time_limit=args.time_limit, relation=args.relation), indent=2))


if __name__ == '__main__':
    main()
