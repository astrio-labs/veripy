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
import dataclasses
import types
import json
from pathlib import Path
import re
import subprocess
import sys

from veripy.backends.base import get_backend
from veripy.backends.dafny.encoder import EncodeError
from veripy.frontend.extract import parse_source
from veripy.frontend.records import record_schemas, RecordError, record_type, record_constructor, record_field
from veripy.backends.dafny.environment import resolve_for_encoder


def _type(node, records=None):
    records = records or {}
    # Match the functional encoder's closed correlated ETag result shape.
    if node is not None and ast.unparse(node) == 'tuple[str, bool] | tuple[None, None]':
        return ('tuple', ('optional', 'str'), ('optional', 'bool'))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        if isinstance(node.right, ast.Constant) and node.right.value is None:
            return ('optional', _type(node.left, records))
        if isinstance(node.left, ast.Constant) and node.left.value is None:
            return ('optional', _type(node.right, records))
    if isinstance(node, ast.Name) and node.id in records:
        return ("record", node.id, tuple((f, _type(t, records)) for f, t in records[node.id]))
    if isinstance(node, ast.Name) and node.id in {'int', 'bool', 'str'}:
        return node.id
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
        if node.value.id == 'Optional':
            return ('optional', _type(node.slice, records))
        if node.value.id == 'list':
            return ('list', _type(node.slice, records))
        if node.value.id == 'tuple' and isinstance(node.slice, ast.Tuple):
            return ('tuple', *(_type(n, records) for n in node.slice.elts))
    raise ValueError(f'comparison boundary at line {getattr(node, "lineno", None)} requires scalars, lists, fixed tuples, or a declared closed frozen record snapshot')


def _signature(source, name):
    environment = resolve_for_encoder(ast.parse(source))
    tree = environment.module
    # The comparison observes a closed module, not a selected definition that
    # could be replaced by later top-level execution.
    records = record_schemas(tree)
    used_names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
    # Legacy extraction may retain unused typing.Union imports. This permits
    # only an unused stdlib annotation import, never an unresolved runtime call.
    def unused_annotation(d):
        return (d['module'] == 'typing' and d['symbol'] == 'Union'
                and d['relative_level'] == 0 and d['binding'] not in used_names)
    if any(d['resolution'] != 'encoder-model' and not unused_annotation(d)
           for d in environment.dependencies):
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
    def default_inhabits(p, d):
        typ = _type(p.annotation, records)
        if isinstance(typ, tuple) and typ[0] == 'optional':
            return d.value is None or typ[1] == type(d.value).__name__
        return typ == type(d.value).__name__
    if any(not default_inhabits(p, d) for p,d in bindings):
        raise ValueError('comparison default must inhabit the exact admitted parameter type')
    parameters = [(p.arg, _type(p.annotation, records), kind) for group, kind in
                  ((a.posonlyargs, 'positional-only'), (a.args, 'positional-or-keyword'),
                   (a.kwonlyargs, 'keyword-only')) for p in group]
    # Equal signatures include exact default ASTs (True must not equal 1).
    # Equal admitted argument values then cover every shared omission pattern.
    default_signature = ([ast.dump(d) for d in a.defaults],
                         [ast.dump(d) if d is not None else None for d in a.kw_defaults])
    return parameters, _type(fn.returns, records), default_signature


def _boundary_type(typ, namespace):
    if isinstance(typ, str):
        return {'int': 'int', 'bool': 'bool', 'str': 'string'}[typ]
    if typ[0] == 'record':
        return namespace + '.' + record_type(typ[1])
    if typ[0] == 'optional':
        return namespace + '.PyOpt<' + _boundary_type(typ[1], namespace) + '>'
    if typ[0] == 'list':
        return 'seq<' + _boundary_type(typ[1], namespace) + '>'
    return '(' + ', '.join(_boundary_type(t, namespace) for t in typ[1:]) + ')'


def _has_record(typ):
    # Optional values also have nominal datatypes in each generated module.
    return not isinstance(typ, str) and (typ[0] in {'record', 'optional'} or any(_has_record(t) for t in typ[1:]))


def _snapshot_value(expr, typ, depth=0):
    """Total structural value map from Old's nominal datatypes to New's.

    Scalars and scalar sequences are already common immutable Dafny values.
    No field is erased and no relation is assumed as an axiom.
    """
    if not _has_record(typ):
        return expr
    if typ[0] == 'record':
        return 'VeriPySnapshot' + typ[1] + '(' + expr + ')'
    if typ[0] == 'optional':
        value = _snapshot_value(f'({expr}).v', typ[1], depth + 1)
        return f'(if ({expr}).PyNone? then New.PyNone else New.PySome({value}))'
    if typ[0] == 'list':
        index = 'veripyIndex' + str(depth)
        item = _snapshot_value(f'({expr})[{index}]', typ[1], depth + 1)
        return f'(seq(|{expr}|, {index} requires 0 <= {index} < |{expr}| => {item}))'
    return '(' + ', '.join(_snapshot_value(f'({expr}).{i}', t, depth + 1)
                           for i, t in enumerate(typ[1:])) + ')'


def _value_equality(left, right, typ, indent='    ', depth=0):
    """Expose structural proof obligations; every emitted step is checked."""
    if not isinstance(typ, str) and typ[0] == 'tuple':
        return ''.join(_value_equality(f'({left}).{i}', f'({right}).{i}', t, indent, depth)
                       for i, t in enumerate(typ[1:]))
    if not isinstance(typ, str) and typ[0] == 'list':
        index = 'veripyEqualityIndex' + str(depth)
        body = _value_equality(f'({left})[{index}]', f'({right})[{index}]', typ[1], indent + '  ', depth + 1)
        return (f'{indent}assert |{left}| == |{right}|;\n'
                f'{indent}forall {index} | 0 <= {index} < |{left}|\n'
                f'{indent}  ensures ({left})[{index}] == ({right})[{index}]\n'
                f'{indent}{{\n{body}{indent}}}\n'
                f'{indent}assert {left} == {right};\n')
    return f'{indent}assert {left} == {right};\n'


def _snapshot_bridges(signature):
    records = {}
    def visit(typ):
        if isinstance(typ, str):
            return
        if typ[0] == 'record':
            for _, field_type in typ[2]:
                visit(field_type)
            records[typ[1]] = typ
        else:
            for t in typ[1:]:
                visit(t)
    for _, typ, _ in signature[0]:
        visit(typ)
    visit(signature[1])
    definitions = []
    for name, typ in records.items():
        fields = ', '.join(_snapshot_value('value.' + record_field(f), t) for f, t in typ[2])
        definitions.append(f'function VeriPySnapshot{name}(value: Old.{record_type(name)}): New.{record_type(name)} {{ New.{record_constructor(name)}({fields}) }}')
    return '\n'.join(definitions) + '\n'


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
    if typ[0] == 'optional':
        return [None, *_samples(typ[1])]
    if typ[0] == 'record':
        fields = typ[2]
        return [dict(zip((f for f, _ in fields), values)) for values in
                itertools.islice(itertools.product(*(_samples(t) for _, t in fields)), 100)]
    if typ[0] == 'list':
        values = _samples(typ[1])
        selected = [values[i * (len(values)-1) // 4] for i in range(5)] if _has_record(typ[1]) else values[:5]
        return [[], *[[v] for v in selected], selected[:3], list(reversed(selected[:3]))]
    return list(itertools.islice(itertools.product(*(_samples(t) for t in typ[1:])), 100))


def _materialize(value, typ, namespace):
    if isinstance(typ, str):
        return value
    if typ[0] == 'optional':
        return None if value is None else _materialize(value, typ[1], namespace)
    if typ[0] == 'record':
        return namespace[typ[1]](**{f: _materialize(value[f], t, namespace) for f, t in typ[2]})
    if typ[0] == 'list':
        return [_materialize(v, typ[1], namespace) for v in value]
    return tuple(_materialize(v, t, namespace) for v, t in zip(value, typ[1:]))


def _observable(value):
    # Independent runtime classes have distinct identities. Compare fields,
    # preserving the structural value observation used by the product proof.
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return {'record': type(value).__name__, 'fields': {
            f.name: _observable(getattr(value, f.name)) for f in dataclasses.fields(value)}}
    if isinstance(value, (list, tuple)):
        return [_observable(v) for v in value]
    return value


def _replay(paths, names, signature):
    functions, pres, namespaces = [], [], []
    for path, name in zip(paths, names):
        source = Path(path).read_text()
        tree = ast.parse(source)
        # Permit only closed schemas and the exact trusted dataclass import.
        # Other modeled imports/default environments remain outside this replay.
        schemas = record_schemas(tree)
        if any(not (isinstance(n, ast.FunctionDef)
                    or isinstance(n, ast.ClassDef) and n.name in schemas
                    or isinstance(n, ast.ImportFrom) and n.level == 0 and n.module == 'dataclasses'
                    and len(n.names) == 1 and n.names[0].name == 'dataclass' and n.names[0].asname is None
                    or isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant) and isinstance(n.value.value, str))
               for n in tree.body):
            return {'reason': 'native replay requires function-only modules or closed frozen record declarations'}
        _signature(source, name)
        module_name = '_veripy_record_replay_' + str(len(functions))
        module = types.ModuleType(module_name)
        sys.modules[module_name] = module
        ns = module.__dict__
        try:
            exec(compile(tree, str(path), 'exec'), ns)
        finally:
            del sys.modules[module_name]
        namespaces.append(ns)
        functions.append(ns[name])
        spec = next(f for f in parse_source(source).functions if f.name == name)
        pres.append([compile(c.desugared, '<requires>', 'eval') for c in spec.by_kind('requires')])
    admitted = 0
    for args in itertools.islice(itertools.product(*(_samples(p[1]) for p in signature)), 1000):
        values_by_version = [tuple(_materialize(copy.deepcopy(v), p[1], ns)
                                   for p, v in zip(signature, args)) for ns in namespaces]
        try:
            accepts = [all(eval(c, {**ns, **dict(zip((p[0] for p in signature), values))}) for c in cs)
                       for cs, ns, values in zip(pres, namespaces, values_by_version)]
        except Exception:
            continue
        if not accepts[0]:
            continue
        admitted += 1
        if not accepts[1]:
            return {'admitted_samples': admitted, 'witness': {'arguments': args, 'kind': 'precondition-narrowing'}}
        results = []
        for fn, native_values in zip(functions, values_by_version):
            try:
                values = copy.deepcopy(native_values)
                positional = [v for p,v in zip(signature,values) if p[2] != 'keyword-only']
                keywords = {p[0]:v for p,v in zip(signature,values) if p[2] == 'keyword-only'}
                results.append({'return': _observable(fn(*positional, **keywords))})
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
        has_records = any(_has_record(p[1]) for p in signatures[0][0]) or _has_record(signatures[0][1])
        if has_records:
            # Use generated names but qualify all nominal old-record types.
            schemas = record_schemas(environments[0].module)
            for schema in sorted(schemas, key=len, reverse=True):
                params = re.sub(r'\b' + re.escape(record_type(schema)) + r'\b', 'Old.' + record_type(schema), params)
            params = re.sub(r'\bPyOpt\b', 'Old.PyOpt', params)
        # Tuple types contain commas: take argument names from the actual
        # generated bindings, rather than splitting their type expressions.
        parameter_names = re.findall(r'(?:^|, )([A-Za-z_][A-Za-z_0-9]*): ', params)
        if set(parameter_names) & {'Old', 'New', 'CompatibilityRelation', 'BackwardCompatible'}:
            raise ValueError('parameter collides with a comparison namespace or relation symbol')
        args = ', '.join(parameter_names)
        if len(parameter_names) != len(signatures[0][0]):
            raise ValueError('generated parameter arity differs from source signature')
        if any(n.startswith('VeriPySnapshot') or n.startswith('veripyIndex') or n.startswith('veripyEqualityIndex') for n in parameter_names):
            raise ValueError('parameter collides with snapshot bridge namespace')
        new_args = ', '.join(_snapshot_value(n, p[1]) for n, p in zip(parameter_names, signatures[0][0]))
        used = set(parameter_names)
        def fresh(base):
            while base in used:
                base += '_'
            used.add(base)
            return base
        old_value, new_value, old_error, new_error = map(fresh, ('oldResult', 'newResult', 'oldError', 'newError'))
        text = ''.join(modules) + '\nimport Old = OldVersion\nimport New = NewVersion\n'
        text += _snapshot_bridges(signatures[0])
        report['record_relation'] = 'total value-preserving Old-to-New snapshot map for records and optional values; preserves presence and all fields; identity and mutable heap excluded' if has_records else None
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
{hint}  assert New.VeriPyCompatibilityAdmitted({new_args});
  var {old_value}{', '+old_error if outcomes[0] else ''} := {calls[0]}({args});
  var {new_value}{', '+new_error if outcomes[1] else ''} := {calls[1]}({new_args});
'''
        if not outcomes[0]:
            text += f'  var {old_error} := false;\n'
        if not outcomes[1]:
            text += f'  var {new_error} := false;\n'
        normal = f'{old_error} == 0' if tagged else f'!{old_error}'
        compared_old = _snapshot_value(old_value, signatures[0][1])
        text += f'  assert {old_error} == {new_error};\n  if {normal} {{\n'
        text += _value_equality(compared_old, new_value, signatures[0][1]) if has_records else f'    assert {compared_old} == {new_value};\n'
        text += '  }\n'
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
            report.update(status='behavioral-difference', witness=report['replay']['witness'],
                          reason='Native replay witnessed an observable difference.' +
                          (' This contradicts the product proof; the proof claim is invalid.' if result.ok else ''))
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
