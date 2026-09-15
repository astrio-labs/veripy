"""Reproducible physical SLOC counts and existing Linux timings for paper tables."""
import ast,hashlib,io,json,re,tokenize
from pathlib import Path
from prose_style import clean_prose
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'paper/evidence'
def python_counts(text):
 tree=ast.parse(text);docs=set()
 for node in ast.walk(tree):
  if isinstance(node,(ast.Module,ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)) and node.body:
   first=node.body[0]
   if isinstance(first,ast.Expr) and isinstance(first.value,ast.Constant) and isinstance(first.value.value,str):docs.add((first.lineno,first.col_offset,first.end_lineno,first.end_col_offset))
 lines=text.splitlines();code=set();spec=set();hints=set()
 for t in tokenize.generate_tokens(io.StringIO(text).readline):
  if t.type==tokenize.COMMENT:
   if t.string.startswith('#@'):
    kind=t.string[2:].strip().split()[0]
    if kind in ('requires','ensures','ghost_ensures'):spec.add(t.start[0])
    elif kind in ('invariant','decreases','proof'):hints.add(t.start[0])
    else:raise ValueError('Unclassified annotation '+kind)
   continue
  if t.type in (tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT):continue
  if t.type==tokenize.STRING and (t.start[0],len(lines[t.start[0]-1][:t.start[1]].encode()),t.end[0],len(lines[t.end[0]-1][:t.end[1]].encode())) in docs:continue
  code.update(n for n in range(t.start[0],t.end[0]+1) if lines[n-1].strip())
 return dict(python_loc=len(code),spec_loc=len(spec),hint_loc=len(hints))
def support_loc(text,backend):
 line='--' if backend=='lean' else '//';start='/-' if backend=='lean' else '/*';end='-/' if backend=='lean' else '*/'
 result=[];i=0;depth=0;quoted=False
 while i<len(text):
  if depth:
   if text.startswith(start,i):depth+=1;i+=2
   elif text.startswith(end,i):depth-=1;i+=2
   else:result.append('\n' if text[i]=='\n' else ' ');i+=1
  elif quoted:
   result.append(text[i])
   if text[i]=='\\' and i+1<len(text):result.append(text[i+1]);i+=2;continue
   if text[i]=='"':quoted=False
   i+=1
  elif text.startswith(line,i):
   while i<len(text) and text[i]!='\n':result.append(' ');i+=1
  elif text.startswith(start,i):depth=1;result.append(' ');i+=2
  else:
   if text[i]=='"':quoted=True
   result.append(text[i]);i+=1
 assert depth==0
 return sum(bool(l.strip()) for l in ''.join(result).splitlines())
assert python_counts('"""doc"""\n# comment\n#@ requires x > 0\ndef f(x: int):\n    """doc"""\n    return "# not a comment"\n')==dict(python_loc=2,spec_loc=1,hint_loc=0)
assert support_loc('-- hi\ndef x := "--" /- outer /- nested -/ end -/\n\n','lean')==1
assert support_loc('// hi\nlemma X() /* outer /* nested */ done */ {}\n','dafny')==1
units=json.loads((ROOT/'case_studies/components.json').read_text());records={}
for p in (ROOT/'case_studies/evidence/linux').glob('*.json'):
 for row in json.loads(p.read_text())['rows']:records[row['component'],row['backend']]=row
rows=[]
for unit in units:
 p=ROOT/unit['lean_source'];assert p.read_bytes()==(ROOT/unit['dafny_source']).read_bytes()
 row=dict(component=unit['component'],source=unit['lean_source'],source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),**python_counts(p.read_text()),support={},seconds={},shared_lean_libraries=[])
 for backend,key,suffix in [('dafny','dafny_source','.proofs.dfy'),('lean','lean_source','.proofs.lean')]:
  sidecar=(ROOT/unit[key]).with_suffix(suffix);text=sidecar.read_text() if sidecar.exists() else ''
  row['support'][backend]={'loc':support_loc(text,backend),'path':str(sidecar.relative_to(ROOT)) if sidecar.exists() else None,'sha256':hashlib.sha256(sidecar.read_bytes()).hexdigest() if sidecar.exists() else None}
  if backend=='lean':row['shared_lean_libraries']=re.findall(r'^-- VERIPY LIBRARY (\S+)',text,re.M)
  record=records[unit['component'],'lean' if backend=='lean' else unit['dafny_backend']]
  assert record['status']=='ok' and record['source_sha256']==row['source_sha256']
  row['seconds'][backend]=record['seconds']
 rows.append(row)
libs={p.stem:{'loc':support_loc(p.read_text(),'lean'),'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in (ROOT/'veripy/backends/lean/library').glob('*.lean')}
result={'method':'Physical nonblank code lines. Python excludes comments/docstrings, includes signatures/imports/types. Spec counts requires/ensures/ghost_ensures comments; Hint counts invariant/decreases/proof comments. Support excludes blank/comment lines but includes all component-sidecar definitions and copied lemmas; shared imported Lean libraries counted separately. No additive cohort total because units overlap. Times are single fresh Linux public-API invocations including encoding and prover startup; not a controlled solver comparison.','rows':rows,'shared_lean_libraries':libs}
(OUT/'component-effort.json').write_text(json.dumps(result,indent=2)+'\n')
selected={'black-composition':('Black: range composition','Exact ordered output'),'sglang-live':('SGLang: live planner','Lengths and reserve'),'pytorch-validation':('PyTorch: shard validation','Overlap and errors'),'django-base36':('Django: base36','Exact digits/errors'),'vllm-padding':('vLLM: padding optimizer','Optimum and tie rule'),'cpython-time-parser':('CPython: time parser','Exact fields/errors'),'luhn-exact':('Luhn: checksum','Exact decimal sum'),'luhn-roundtrip':('Luhn: check digit','Decimal round trip'),'luhn-validation':('Luhn: validation','Bounds/error classes')}
def escaped(s):return s.replace('_',r'\_')
def body(row,label,prop=None):
 parts=[escaped(label),str(row['python_loc']),str(row['spec_loc']),str(row['hint_loc']),f"{row['support']['dafny']['loc']} / {row['support']['lean']['loc']}",f"{row['seconds']['dafny']:.2f} / {row['seconds']['lean']:.2f}"]
 if prop is not None:parts.append(prop)
 return ' & '.join(parts)+r' \\'
header=r'''\begin{table}[t]
\caption{Component verification and support for nine selected units. Py: Python LOC;
Spec: contract LOC; Hint: inline proof-hint LOC. Support and time pairs are
Dafny / Lean. Support includes sidecar definitions and copied lemmas, excluding
shared imported libraries. All rows pass both backends. The complete 25-unit
inventory and counting rules are in Appendix~\ref{app:effort}.}
\label{tab:parity}
\centering\small
\begin{tabularx}{\linewidth}{@{}lrrrllX@{}}
\toprule
Component & Py & Spec & Hint & Support & Time (s) & Property \\
\midrule
'''
byname={r['component']:r for r in rows}
main=header+'\n'.join(body(byname[k],*v) for k,v in selected.items())+'\n'+r'\bottomrule'+'\n'+r'\end{tabularx}'+'\n'+r'\end{table}'+'\n'
(ROOT/'paper/sections/component-effort-main.tex').write_text(clean_prose(main))
appendix=r'''\clearpage
\section{Component size and proof support}
\label{app:effort}

Counts are physical nonblank lines. Python LOC excludes comments and docstrings
but includes signatures, type annotations, imports and executable assertions.
Spec counts \texttt{requires}, \texttt{ensures} and \texttt{ghost\_ensures} annotation
lines; Hint counts invariants, decreases clauses and proof hooks. Sidecar support
counts all noncomment lines, including specification definitions and reused
lemmas; it is not a count of newly authored proof lines or human effort.
The component-specific sidecars exclude imported shared libraries and generated
backend models/preambles. Shared imported Lean libraries contain '''+', '.join(f"{v['loc']} LOC ({k})" for k,v in sorted(libs.items()))+r'''.
Their use is recorded per unit in \texttt{evidence/component-effort.json}.
Copied support remains in each sidecar's count. No total is given because units
and their helpers overlap. Zero sidecar support does not imply zero manual work.

Times come from the same fresh Linux CI checkpoint, one public-API invocation per
unit/backend, including encoding and prover startup. Groups ran on separate CI
runners; these observations are offline costs, not a fair backend-speed ranking
or application-runtime overhead. The counting script and hashed sources are
included in the supplement.

\begin{table}[h]
\caption{All 25 paired units under the same counting policy. D / L denotes
Dafny / Lean. Every unit passed both backends.}
\centering\small
\begin{tabular}{@{}lrrrrl@{}}
\toprule
Unit & Py & Spec & Hint & Support D / L & Time D / L (s) \\
\midrule
'''
appendix+='\n'.join(body(row,row['component']) for row in rows)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n'+r'\end{table}'+'\n'
(ROOT/'paper/sections/component-effort-appendix.tex').write_text(clean_prose(appendix.removeprefix('\\clearpage\n')))
print('Measured',len(rows),'units; shared libraries', {k:v['loc'] for k,v in libs.items()})
