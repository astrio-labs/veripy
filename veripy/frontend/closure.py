"""Static, source-preserving candidate extraction for annotated components.

This is a preparation tool, never an admission or compatibility verdict. It
retains referenced declarations and reports import/model boundaries. It does
not import Python packages, execute initializers, infer types or add contracts.
The caller must independently admit and verify the candidate under a closed
module environment; enclosing-module initialization is not proved here.
"""
from __future__ import annotations
import ast
import builtins
import hashlib
import symtable
from ..backends.dafny.dependencies import inventory

# These names are recognized by the existing isolated historical adapter. This
# inventory is descriptive: even these builtins require operation-level admission.
MODELED_BUILTINS = frozenset(('abs all any bool divmod enumerate int len list max min '
                            'range reversed sorted str sum tuple zip ValueError').split())


def _globals(table):
    names={s.get_name() for s in table.get_symbols() if s.is_global() and s.is_referenced()}
    for child in table.get_children():names.update(_globals(child))
    return names


def _bound(node):
    if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)):
        return {node.name}
    if isinstance(node,(ast.Import,ast.ImportFrom)):
        return {a.asname or (a.name.split('.')[0] if isinstance(node,ast.Import) else a.name) for a in node.names}
    if isinstance(node,(ast.Assign,ast.AnnAssign,ast.AugAssign,ast.Delete)):
        targets=(node.targets if isinstance(node,(ast.Assign,ast.Delete)) else [node.target])
        names={x.id for target in targets for x in ast.walk(target)
               if isinstance(x,ast.Name) and isinstance(x.ctx,(ast.Store,ast.Del))}
        # Assignment expressions in initializer comprehensions bind in the
        # enclosing module; ordinary comprehension targets do not.
        names.update(x.target.id for x in ast.walk(node) if isinstance(x,ast.NamedExpr))
        return names
    names=set()
    if isinstance(node,(ast.For,ast.AsyncFor)):
        names.update(x.id for x in ast.walk(node.target) if isinstance(x,ast.Name) and isinstance(x.ctx,ast.Store))
    if isinstance(node,ast.ExceptHandler) and node.name:names.add(node.name)
    for child in ast.iter_child_nodes(node):
        if isinstance(child,(ast.stmt,ast.ExceptHandler)):names.update(_bound(child))
        elif isinstance(child,ast.withitem) and child.optional_vars:
            names.update(x.id for x in ast.walk(child.optional_vars) if isinstance(x,ast.Name) and isinstance(x.ctx,ast.Store))
    return names


def _references(node):
    # Python's symbol table handles nested comprehensions and closures correctly.
    # The top-level referenced symbols additionally include defaults, decorators,
    # bases and eager annotations, which the old function-only check omitted.
    text=ast.unparse(node)
    # Python 3.12 inlines comprehensions at module scope, marking their target
    # names global in symtable. Analyze initializer expressions in a function
    # scope so those temporary binders cannot become invented dependencies.
    if isinstance(node,(ast.Assign,ast.AnnAssign)) and node.value is not None:
        text='def __closure_initializer__():\n    return '+ast.unparse(node.value)
    table=symtable.symtable(text,'<dependency>','exec')
    names=_globals(table)
    # Quoted annotations have no symbol-table references but must not silently
    # lose the declaration needed to interpret them in a typed candidate.
    annotations=[]
    for n in ast.walk(node):
        if isinstance(n,ast.arg) and n.annotation is not None:annotations.append(n.annotation)
        elif isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.returns is not None:annotations.append(n.returns)
        elif isinstance(n,ast.AnnAssign):annotations.append(n.annotation)
    for annotation in annotations:
        names.update(n.id for n in ast.walk(annotation) if isinstance(n,ast.Name))
        for n in ast.walk(annotation):
            if isinstance(n,ast.Constant) and isinstance(n.value,str):
                try:quoted=ast.parse(n.value,mode='eval')
                except SyntaxError:continue
                names.update(x.id for x in ast.walk(quoted) if isinstance(x,ast.Name))
    return names


def extract_candidate(source: str, entry: str) -> dict:
    """Return a reviewable candidate plus provenance, or explicit blockers.

    Source line numbers and retained ASTs are unchanged. Ambiguous/rebound names,
    star imports and non-declaration bindings fail closed. External imports and
    unmodeled builtins remain visible and are NOT granted contracts by extraction.
    """
    tree=ast.parse(source)
    declarations={};imports={};issues=[]
    simple=(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef,ast.Assign,ast.AnnAssign,ast.Import,ast.ImportFrom)
    for n in tree.body:
        for name in _bound(n):declarations.setdefault(name,[]).append(n)
        for item in inventory(ast.Module(body=[n],type_ignores=[])):
            imports[(n.lineno,item['binding'])]=item
        if isinstance(n,ast.ImportFrom) and any(a.name=='*' for a in n.names):
            issues.append({'kind':'wildcard-import','line':n.lineno,'name':'*'})
    selected={};edges=[];nodes={};pending=[entry];seen=set()
    while pending:
        name=pending.pop()
        if name in seen:continue
        seen.add(name)
        bindings=declarations.get(name,[])
        if len(bindings)>1:
            nodes[name]={'kind':'ambiguous-binding','lines':[n.lineno for n in bindings]}
            issues.append({'kind':'ambiguous-binding','name':name});continue
        if not bindings:
            if name in vars(builtins) and not name.startswith("__"):
                nodes[name]={'kind':'builtin','modeled_surface':name in MODELED_BUILTINS}
            else:
                nodes[name]={'kind':'unresolved'};issues.append({'kind':'unresolved','name':name})
            continue
        n=bindings[0]
        if not isinstance(n,simple):
            nodes[name]={'kind':'dynamic-binding','line':n.lineno}
            issues.append({'kind':'dynamic-binding','name':name,'line':n.lineno});continue
        kind=('local-function' if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) else
              'local-class' if isinstance(n,ast.ClassDef) else 'import' if isinstance(n,(ast.Import,ast.ImportFrom)) else 'module-value')
        nodes[name]={'kind':kind,'line':n.lineno,'end_line':n.end_lineno}
        if kind=='import':nodes[name]['import']=imports.get((n.lineno,name))
        selected[n.lineno]=n
        if kind!='import':
            refs=_references(n)
            for dep in sorted(refs):
                edges.append({'from':name,'to':dep});pending.append(dep)
        # Global/nonlocal rebinding inside a retained body is outside the closed
        # environment. A same-name recursive read alone is not a rebinding.
        if any(isinstance(x,(ast.Global,ast.Nonlocal)) for x in ast.walk(n)):
            issues.append({'kind':'nonlocal-state','name':name,'line':n.lineno})
    if entry not in declarations or len(declarations[entry])!=1 or not isinstance(declarations[entry][0],ast.FunctionDef):
        issues.append({'kind':'entry-must-be-unique-function','name':entry})
    # Detect explicit module-level mutation of any retained declaration even if
    # that statement binds no names (e.g. TABLE[0] = 7, helper.attr = value).
    for n in tree.body:
        if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)):continue
        for x in ast.walk(n):
            if isinstance(x,(ast.Subscript,ast.Attribute)) and isinstance(x.ctx,(ast.Store,ast.Del)):
                base=x.value
                while isinstance(base,(ast.Subscript,ast.Attribute)):base=base.value
                if isinstance(base,ast.Name) and base.id in seen:
                    issues.append({'kind':'module-mutation','name':base.id,'line':n.lineno})
            if isinstance(x,ast.Call) and isinstance(x.func,ast.Attribute):
                base=x.func.value
                if isinstance(base,ast.Name) and base.id in seen and n.lineno not in selected:
                    issues.append({'kind':'module-call-on-dependency','name':base.id,'line':n.lineno})
    # Keep future annotation semantics. Imports preserve their original full
    # declaration, so report collateral imports as well as referenced aliases.
    for n in tree.body:
        if isinstance(n,ast.ImportFrom) and n.module=='__future__':selected[n.lineno]=n
    candidate=None
    if not issues:
        lines=source.splitlines(keepends=True);keep=set()
        for n in selected.values():
            start=min([n.lineno,*[d.lineno for d in getattr(n,'decorator_list',[])]])-1
            while start>0 and (not lines[start-1].strip() or lines[start-1].lstrip().startswith('#')):start-=1
            keep.update(range(start,n.end_lineno))
        candidate=''.join(line if i in keep else '\n' for i,line in enumerate(lines))
        extracted=ast.parse(candidate)
        expected=[ast.dump(selected[k],include_attributes=False) for k in sorted(selected)]
        assert [ast.dump(n,include_attributes=False) for n in extracted.body]==expected
    return {'schema':1,'entry':entry,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
            'status':'blocked' if issues else 'extracted','verification_status':'not-run',
            'nodes':dict(sorted(nodes.items())),'edges':sorted(edges,key=lambda e:(e['from'],e['to'])),
            'issues':issues,'retained_lines':sorted(selected),'candidate_source':candidate,
            'candidate_sha256':hashlib.sha256(candidate.encode()).hexdigest() if candidate is not None else None,
            'imports':inventory(ast.Module(body=[n for k in sorted(selected) for n in ast.walk(selected[k]) if isinstance(n,(ast.Import,ast.ImportFrom))],type_ignores=[])),
            'scope':'Declaration-view preparation only; module initialization and external dependencies require independent admission. No types, specifications or proof authority are inferred.'}


def main():
    """Write candidate and diagnostics to a fresh directory; never run it."""
    import argparse
    import json
    from pathlib import Path
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('--function',required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    result=extract_candidate(args.source.read_text(),args.function)
    args.out.mkdir(parents=True,exist_ok=False)
    source=result.pop('candidate_source')
    if source is not None:(args.out/'candidate.py').write_text(source)
    (args.out/'dependencies.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'verification_status':'not-run','output':str(args.out)}))
    return 0 if result['status']=='extracted' else 1


if __name__=='__main__':raise SystemExit(main())
