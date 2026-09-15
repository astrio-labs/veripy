"""Descriptive maintenance metrics; default regeneration uses packaged inputs.

--collect reads the audited raw run and captures normalized measured fields.
It does not execute models/provers or modify any historical experiment record.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import statistics

ROOT=Path(__file__).resolve().parents[2]
E=ROOT/'paper/evidence'
ARCHIVE_ROOT=None
RUN=None
INPUT=E/'maintenance-metric-inputs.json'

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def collect():
    assert RUN is not None and ARCHIVE_ROOT is not None
    audit=read(RUN/'maintenance-audit.json')
    assert not audit['errors'] and len(audit['trials'])==48
    calls=[]
    for row in audit['calls']:
        if row['category']!='maintenance':continue
        path=RUN/row['path'];parts=Path(row['path']).parts
        rep,arm=parts[3].split('-',1)
        record=read(path);receipt_path=path.parent.parent/'check/receipt.json';receipt=read(receipt_path)
        assert record['elapsed_s']==row['elapsed_s']
        calls.append({'id':parts[1],'rep':int(rep),'arm':arm,'response_index':int(parts[4]),
                      'source':row['path'],'source_sha256':sha(path),'receipt_sha256':sha(receipt_path),
                      'usage':record['usage'],'actual_cost_usd':record['actual_cost_usd'],
                      'model_seconds':record['elapsed_s'],'checker_seconds':receipt['seconds']})
    assert len(calls)==80
    assert abs(sum(c['checker_seconds'] for c in calls)-audit['checker_elapsed_s'])<1e-6
    analysis=read(RUN/'analysis.json')
    save(INPUT,{'scope':'Normalized fields from the 48 audited controlled maintenance trials and 80 model/checker receipts; raw hashes identify extraction sources. Excludes authoring, isolation, old-proof preparation and later diagnostics from arm costs.',
                'source_hashes':{str(p.relative_to(ARCHIVE_ROOT)):sha(p) for p in [RUN/'maintenance-audit.json',RUN/'failure-analysis.json',RUN/'analysis.json']},
                'components':[{k:r[k] for k in ['case','label','old_support_contrast']} for r in analysis['components']],
                'trials':audit['trials'],'calls':calls,'failure_rows':read(RUN/'failure-analysis.json')['rows'],
                'library_control':read(RUN.parent/'library-diagnostic-01/maintenance-audit.json')['arm_summary']})

def metrics(rows,calls,failures):
    n=len(rows);success=[r for r in rows if r['status']=='proved'];ids=sorted({r['id'] for r in rows})
    assert len({(r['id'],r['rep'],r['arm']) for r in rows})==n
    assert len(calls)==sum(r['responses'] for r in rows)
    for r in rows:
        cc=[c for c in calls if (c['id'],c['rep'],c['arm'])==(r['id'],r['rep'],r['arm'])]
        assert sorted(c['response_index'] for c in cc)==list(range(r['responses']))
    return {'trials':n,'joint_proofs':len(success),'joint_rate':len(success)/n,
            'first_response_proofs':sum(r['responses']==1 for r in success),
            'within_two_response_proofs':sum(r['responses']<=2 for r in success),
            'updates':len(ids),'updates_proved_both_repetitions':sum(all(r['status']=='proved' for r in rows if r['id']==i) for i in ids),
            'responses':len(calls),'responses_per_trial':len(calls)/n,
            'model_seconds_sum':sum(c['model_seconds'] for c in calls),
            'checker_seconds_sum':sum(c['checker_seconds'] for c in calls),
            'model_seconds_median_per_trial':statistics.median(sum(c['model_seconds'] for c in calls if (c['id'],c['rep'],c['arm'])==(r['id'],r['rep'],r['arm'])) for r in rows),
            'usage':{k:sum(c['usage'][k] for c in calls) if all(c['usage'] and c['usage'].get(k) is not None for c in calls) else None for k in ('input_tokens','cached_input_tokens','output_tokens','reasoning_output_tokens')},
            'actual_cost_usd':sum(c['actual_cost_usd'] for c in calls) if all(c['actual_cost_usd'] is not None for c in calls) else None,
            'failure_categories':dict(collections.Counter(r['diagnostic_category'] for r in failures))}

def main():
    global ARCHIVE_ROOT, RUN
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect',action='store_true')
    parser.add_argument('--archive-root',type=Path,help='Extracted historical archive root containing the original case_studies directory')
    args=parser.parse_args()
    if args.collect:
        if args.archive_root is None:
            parser.error('--collect requires --archive-root; ordinary regeneration uses packaged metric inputs')
        ARCHIVE_ROOT=args.archive_root.resolve()
        RUN=ARCHIVE_ROOT/'case_studies/research_evaluation_v2/controlled-01'
        if not (RUN/'maintenance-audit.json').is_file():
            parser.error('The archive root does not contain the original controlled maintenance records')
        collect()
    d=read(INPUT);trials=d['trials'];calls=d['calls'];arms={}
    for arm in ('reuse','rebuild'):
        arms[arm]=metrics([r for r in trials if r['arm']==arm],[c for c in calls if c['arm']==arm],[r for r in d['failure_rows'] if r['arm']==arm])
    pairs=[]
    for id in sorted({r['id'] for r in trials}):
        for rep in (0,1):
            pair={r['arm']:r for r in trials if r['id']==id and r['rep']==rep}
            assert len(pair)==2
            pairs.append(pair)
    both=[p for p in pairs if all(r['status']=='proved' for r in p.values())]
    paired={'both_proved':len(both),'reuse_only':sum(p['reuse']['status']=='proved' and p['rebuild']['status']!='proved' for p in pairs),
            'rebuild_only':sum(p['rebuild']['status']=='proved' and p['reuse']['status']!='proved' for p in pairs),
            'neither':sum(all(r['status']!='proved' for r in p.values()) for p in pairs),
            'common_success_response_totals':{a:sum(p[a]['responses'] for p in both) for a in arms}}
    grouped=[]
    for c in d['components']:
        ids={r['id'] for r in trials if r['id'].rsplit('-',1)[0]==c['case']}
        grouped.append({**c,'arms':{a:metrics([r for r in trials if r['id'] in ids and r['arm']==a],[v for v in calls if v['id'] in ids and v['arm']==a],[r for r in d['failure_rows'] if r['id'] in ids and r['arm']==a]) for a in arms}})
    result={'input_sha256':sha(INPUT),'arms':arms,'paired_trials':paired,'components':grouped,
            'interpretation':'Descriptive, clustered by update/component; no independence assumption or significance claim. Response and time totals include failures with different stopping conditions. Common-success costs are conditional. Token fields may overlap and are not additive categories. Dollar billing unknown. The separately frozen public-library diagnostic passes 4/4 per arm in one response; primary differences do not isolate proof reuse.'}
    save(E/'maintenance-metrics.json',result)
    tex=[r'\begin{table}[t]',r'\centering\small',r'\caption{Twelve agent-authored updates, each repeated twice per arm. Joint proof means functional correctness and compatibility. First response counts joint proofs completed after one model response. Asterisks mark controls without private old proof support. Responses include failures.}',r'\label{tab:controlled-maintenance}',r'\begin{tabular}{@{}lrrrrrr@{}}',r'\toprule',r'& \multicolumn{2}{c}{Joint proofs} & \multicolumn{2}{c}{First response} & \multicolumn{2}{c}{Responses} \\',r'Component & Reuse & Rebuild & Reuse & Rebuild & Reuse & Rebuild \\',r'\midrule']
    for row in grouped+[{'label':'Total','old_support_contrast':True,'arms':arms}]:
        a,b=row['arms'].values();label=row['label']+(r'$^*$' if not row['old_support_contrast'] else '')
        if label=='Total':tex.append(r'\midrule')
        tex.append(f'{label} & {a["joint_proofs"]}/{a["trials"]} & {b["joint_proofs"]}/{b["trials"]} & {a["first_response_proofs"]}/{a["trials"]} & {b["first_response_proofs"]}/{b["trials"]} & {a["responses"]} & {b["responses"]} '+r'\\')
    tex += [r'\bottomrule',r'\end{tabular}',r'\end{table}']
    from prose_style import clean_prose
    (ROOT/'paper/sections/controlled-maintenance-table.tex').write_text(clean_prose('\n'.join(tex)+'\n').replace('\\begin{table}[t]', '\\begin{table}[ht]'))
    lines=[r'\clearpage',r'\subsection{Additional descriptive maintenance metrics}',r'\label{app:maintenance-metrics}',r'These metrics describe the same 48 maintenance trials, not additional experiments. Each arm has 24 trials on 12 updates, with two repetitions per update. Costs cover maintenance responses only, excluding change generation, isolation, old-proof preparation, and the later library diagnostic.',r'\begin{table}[h]',r'\centering\small',r'\caption{Completion, effort and final failure categories for the controlled study.}',r'\begin{tabular}{@{}lrr@{}}',r'\toprule',r'Metric & Reuse & Rebuild \\',r'\midrule']
    def row(label,key,fmt=str):lines.append(label+' & '+' & '.join(fmt(arms[a][key]) for a in arms)+r' \\')
    row('Joint proof rate','joint_rate',lambda v:f'{100*v:.1f}'+r'\%')
    row('Updates proved in both repetitions (of 12)','updates_proved_both_repetitions')
    row('Joint proofs within one response (of 24)','first_response_proofs')
    row('Joint proofs within two responses (of 24)','within_two_response_proofs')
    row('Joint proofs within three responses (of 24)','joint_proofs')
    row('Total model responses','responses')
    row('Mean responses per trial','responses_per_trial',lambda v:f'{v:.2f}')
    lines.append('Responses on 10 jointly successful pairs & '+' & '.join(str(paired['common_success_response_totals'][a]) for a in arms)+r' \\')
    row('Summed model-call seconds','model_seconds_sum',lambda v:f'{v:,.1f}')
    row('Median model-call seconds per trial','model_seconds_median_per_trial',lambda v:f'{v:.1f}')
    row('Summed checker seconds','checker_seconds_sum',lambda v:f'{v:,.1f}')
    for k,label in [('input_tokens','Reported input tokens'),('cached_input_tokens','Reported cached-input tokens'),('output_tokens','Reported output tokens'),('reasoning_output_tokens','Reported reasoning tokens')]:
        lines.append(label+' & '+' & '.join(f'{arms[a]["usage"][k]:,}' for a in arms)+r' \\')
    lines.append(r'Actual dollar billing & Unknown & Unknown \\');lines.append(r'\midrule')
    for k,label in [('strict-typing','Final failure: strict typing'),('encoding-or-specification','Final failure: encoding/specification'),('backend-model-typing-or-resolution','Final failure: backend typing/resolution'),('unproved-obligation','Final failure: unproved obligation')]:
        lines.append(label+' & '+' & '.join(str(arms[a]['failure_categories'].get(k,0)) for a in arms)+r' \\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{table}',
              'Of 24 paired repetitions, 10 succeed in both arms, 4 only with reuse, none only with rebuild, and 10 in neither. These correspond to five, two, zero and five distinct updates; repetitions agree on completion and are not independent samples.',
              'Time totals sum individual call durations, not experiment makespan or pure solver time. Failed trials may stop at strict typing or exhaust the response budget; their lower costs do not indicate better verification. Common-success costs are conditional on both arms completing. Reported token fields can overlap, particularly reasoning and output fields; they are not added into a billed total.',
              'The separately frozen public-library diagnostic supplies regex definitions equally: both arms prove 4/4 Packaging trials in one response each. The primary completion gap and these response metrics therefore do not isolate a general proof-reuse advantage. No significance test or broader generalization follows from this small, clustered cohort.']
    body='\n\n'.join(lines)+'\n'
    start=body.index(r'\begin{tabular}');end=body.index(r'\end{tabular}')
    body=body[:start]+body[start:end].replace('\n\n','\n')+body[end:]
    body=clean_prose(body).replace('\\begin{table}[h]', '\\input{sections/controlled-maintenance-table}\n\n\\begin{table}[h]', 1)
    (ROOT/'paper/sections/maintenance-metrics-appendix.tex').write_text(body)
    print(json.dumps(arms,indent=2))

if __name__=='__main__':main()
