"""Kernel-check concrete violations of the frozen full generated contracts.

The execution equality and negated postcondition are both proved. No proof
search timeout or native execution alone is counted as a certified violation.
"""
from pathlib import Path
import hashlib,json,time,sys
from veripy.backends.lean.imperative import encode_imperative
from veripy.backends.lean.driver import verify_lean_file
from veripy.frontend.extract import parse_source
HERE=Path(__file__).resolve().parents[1]/'cpython'
out=HERE/(sys.argv[1] if len(sys.argv)>1 else 'kernel-mutation-certificates');out.mkdir(exist_ok=False)
rows=[]
for name,text in [('field-value','12:34:56'),('fraction-scale','12:34:56.1'),('fraction-truncation','12:34:56.123456'),('separator','12:34:56')]:
    src=HERE/'mutations'/f'{name}.py';source=src.read_text();ns={};exec(source,ns)
    try:actual=ns['_parse_hh_mm_ss_ff'](text);error=False
    except ValueError:actual='ValueError';error=True
    model=encode_imperative(source,parse_source(source),name+'.py').lean_source.split('-- VERIPY IMPERATIVE PROOF SUPPORT')[0]
    inp='['+','.join(map(str,map(ord,text)))+']'
    value='VeriPy.Error.value' if error else '['+','.join(map(str,actual))+']'
    result=('Except.error ' if error else 'Except.ok ')+value
    pred='«_parse_hh_mm_ss_ff__error»' if error else '«_parse_hh_mm_ss_ff__post»'
    proof=f'\ntheorem mutation_execution : «_parse_hh_mm_ss_ff» {inp} = {result} := by rfl\n'
    proof+=f'theorem mutation_violates : ¬ ({pred} {inp} {value}) := by\n'
    facts=[]
    for lo,hi in [(0,2),(3,5),(6,8),(9,len(text)),(9,15)]:
        if hi<lo:continue
        try:decimal='some ('+str(int(text[lo:hi]))+')'
        except ValueError:decimal='none'
        nm=f'hd{lo}_{hi}'
        if nm in facts:continue
        proof+=f'  have {nm} : VeriPy.tryDecimal (VeriPy.slice {inp} {lo} {hi}) = {decimal} := by rfl\n';facts.append(nm)
    for lo in [2,5]:
        chars='['+','.join(map(str,map(ord,text[lo:lo+1])))+']';nm=f'hs{lo}'
        proof+=f'  have {nm} : VeriPy.slice {inp} {lo} {lo+1} = {chars} := by rfl\n';facts.append(nm)
    proof+='  simp ['+pred+', '+', '.join(facts)+']\n'
    proof+=f'''theorem mutation_counterexample :
    match «_parse_hh_mm_ss_ff» {inp} with
    | Except.ok result => ¬ («_parse_hh_mm_ss_ff__post» {inp} result)
    | Except.error err => ¬ («_parse_hh_mm_ss_ff__error» {inp} err) := by
  rw [mutation_execution]
  exact mutation_violates
#print axioms mutation_counterexample
'''
    path=out/f'{name}.lean';path.write_text(model+'\n'+proof)
    start=time.monotonic();r=verify_lean_file(path,{},time_limit=120,stub_extent=None)
    (out/f'{name}.log').write_text(r.raw)
    row={'mutation':name,'input':text,'actual':actual,'status':'certified' if r.ok else 'failed','source_sha256':hashlib.sha256(source.encode()).hexdigest(),'model_and_certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'axiom_messages':[d.message for d in r.diagnostics if 'axioms' in d.message], 'errors':[d.message for d in r.diagnostics if d.severity=='error']}
    rows.append(row);(out/'summary.json').write_text(json.dumps(rows,indent=2)+'\n');print({k:v for k,v in row.items() if k!='errors'},flush=True)
assert all(r['status']=='certified' for r in rows), 'Inspect failed certificate checks'
