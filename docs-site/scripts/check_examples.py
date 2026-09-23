"""Execute the exact tutorial code blocks with real proof backends."""
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[2]
def block(page, language, index=0):
    text=(ROOT/'docs/guide'/f'{page}.md').read_text()
    return re.findall(r'^```'+language+r'[^\n]*\n(.*?)^```',text,re.M|re.S)[index]
def run(args, expected=0):
    p=subprocess.run([sys.executable, *args],cwd=ROOT,text=True,capture_output=True,timeout=180)
    if p.returncode!=expected:raise AssertionError(f'{args}\n{p.stdout}\n{p.stderr}')
    return p
for tool in ('dafny','lean','basedpyright'):
    if not shutil.which(tool):raise SystemExit(f'Missing tutorial validation tool: {tool}')
with tempfile.TemporaryDirectory(prefix='veripy-docs-') as tmp:
    out=Path(tmp)
    for page in ('first-proof','contracts','loops','proof-support'):
        source=out/(page+'.py');source.write_text(block(page,'python'))
        if page=='proof-support':source.with_suffix('.proofs.dfy').write_text(block(page,'dafny'))
        run(['-m','veripy','check',str(source)])
        run(['-m','veripy','verify',str(source),'--time-limit','30','--outdir',str(out/(page+'-proof'))])
        if page=='first-proof':
            report=out/'lean/result.json'
            run(['-m','veripy','verify',str(source),'--backend','lean','--json',str(report),'--time-limit','30'])
            assert json.loads(report.read_text())[0]['status']=='ok'
            run(['-m','veripy','guard',str(source),'--check-ensures','--outdir',str(out/'guard')])
            source.write_text(source.read_text().replace('return x + 1','return x + 2'))
            run(['-m','veripy','verify',str(source),'--time-limit','30','--outdir',str(out/'bad-proof')],expected=1)
        if page=='loops':
            source.write_text(source.read_text().replace('total += 1','total += 2'))
            run(['-m','veripy','verify',str(source),'--time-limit','30','--outdir',str(out/'bad-loop')],expected=1)
        print(f'{page}: passed',flush=True)
    old=out/'old.py';new=out/'new.py'
    old.write_text(block('compatibility','python',0));new.write_text(block('compatibility','python',1))
    p=run(['-m','veripy.compatibility','--old',str(old),'--new',str(new),'--function','increment','--backend','dafny-outcomes','--out',str(out/'comparison')])
    assert 'proved-compatible' in p.stdout,p.stdout
    print('compatibility: passed',flush=True)
