"""Portable dual-backend verification with process-group walls and retained evidence."""
import argparse,concurrent.futures,hashlib,json,os,signal,subprocess,sys,time,unicodedata
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run_bounded(command,wall,cwd):
    start=time.monotonic()
    proc=subprocess.Popen(command,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
    timed_out=False
    try:output=proc.communicate(timeout=wall)[0]
    except subprocess.TimeoutExpired:
        timed_out=True
        os.killpg(proc.pid,signal.SIGKILL)
        output=proc.communicate()[0]
    return proc.returncode,output,time.monotonic()-start,timed_out

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--components',nargs='+');p.add_argument('--backends',nargs='+',choices=['lean','dafny'],default=['lean','dafny']);p.add_argument('--workers',type=int,default=1);p.add_argument('--wall',type=int,default=900);p.add_argument('--repetitions',type=int,default=1);a=p.parse_args()
    rows=json.loads((HERE.parent/'components.json').read_text());names={r['component'] for r in rows}
    if a.components:
        assert set(a.components)<=names,set(a.components)-names
        rows=[r for r in rows if r['component'] in a.components]
    if any(r['component'].startswith('black-') for r in rows):
        assert unicodedata.unidata_version=='15.0.0' and sys.get_int_max_str_digits()==4300,'Black requires Python Unicode15 and digit limit4300'
    out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
    compiler={str(p.relative_to(ROOT)):sha(p) for p in sorted((ROOT/'veripy').rglob('*')) if p.suffix in ['.py','.lean']}
    input_paths=set()
    for row in rows:
        for backend,suffix in [('dafny','.proofs.dfy'),('lean','.proofs.lean')]:
            source=ROOT/row[backend+'_source']
            input_paths.update([source,source.with_suffix(suffix)])
    def input_hashes():
        return {str(path.relative_to(ROOT)):sha(path) if path.exists() else None for path in sorted(input_paths)}
    inputs=input_hashes()
    manifest={'compiler_sha256':compiler,'python':sys.version,'workers':a.workers,'wall_seconds':a.wall,'repetitions':a.repetitions,'measurement':'Fresh public-API verification, including encoding and prover startup. Sequential by default; timings under concurrency are not a controlled speed comparison.','rows':[]}
    manifest['input_sha256']=inputs
    def run(item):
        row,backend,repeat=item;source=ROOT/row[backend+'_source'];other=ROOT/row[('dafny' if backend=='lean' else 'lean')+'_source'];assert source.read_bytes()==other.read_bytes()
        assert input_hashes()==inputs, 'Proof inputs changed during the run'
        dest=out/f"{row['component']}-{backend}-{repeat:02}";dest.mkdir()
        selected=row['dafny_backend'] if backend=='dafny' else 'lean'
        code='''import json,sys\nfrom pathlib import Path\nfrom veripy.api import verify\nr=verify(Path(sys.argv[1]),Path(sys.argv[2]),backend=sys.argv[4],time_limit=int(sys.argv[5]),keep_artifacts=True);Path(sys.argv[3]).write_text(json.dumps(r,indent=2)+"\\n")'''
        status,output,seconds,timeout=run_bounded([sys.executable,'-c',code,str(source),str(dest/'artifacts'),str(dest/'verification.json'),selected,str(a.wall)],a.wall+15,ROOT)
        (dest/'process.log').write_text(output)
        r=json.loads((dest/'verification.json').read_text()) if (dest/'verification.json').exists() else {}
        sidecar=source.with_suffix('.proofs.lean' if backend=='lean' else '.proofs.dfy')
        return {'component':row['component'],'backend':selected,'repeat':repeat,'status':'wall-timeout' if timeout else r.get('status','process-error'),'exit_code':status,'seconds':seconds,'source_sha256':sha(source),'source':str(source.relative_to(ROOT)),'source_byte_identical':True,'support_lines':len(sidecar.read_text().splitlines()) if sidecar.exists() else 0,'annotation_lines':sum(l.lstrip().startswith('#@') for l in source.read_text().splitlines()),'source_lines':len(source.read_text().splitlines()),'report':str((dest/'verification.json').relative_to(out)),'toolchain':r.get('toolchain'),'axiom_audit':r.get('axiom_audit')}
    items=[(r,b,i) for i in range(a.repetitions) for r in rows for b in a.backends]
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
        for row in pool.map(run,items):
            manifest['rows'].append(row);(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(row['component'],row['backend'],row['status'],round(row['seconds'],2),flush=True)
    manifest['all_passed']=all(r['status']=='ok' and r['exit_code']==0 for r in manifest['rows'])
    manifest['compiler_unchanged']=compiler=={str(p.relative_to(ROOT)):sha(p) for p in sorted((ROOT/'veripy').rglob('*')) if p.suffix in ['.py','.lean']}
    manifest['inputs_unchanged']=inputs==input_hashes()
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return 0 if manifest['all_passed'] and manifest['compiler_unchanged'] and manifest['inputs_unchanged'] else 1
if __name__=='__main__':raise SystemExit(main())
