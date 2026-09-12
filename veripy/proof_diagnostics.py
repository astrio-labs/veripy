"""Describe controlled annotation-deletion observations without proof claims."""
from __future__ import annotations
from collections import Counter
from typing import Any


def verification_summary(observation: dict[str, Any]) -> dict[str, Any]:
    v = observation.get('verification')
    if v is None:
        return {'status': 'not_run_guard_rejection', 'guard': observation['guard']}
    errors = [d for d in v.get('diagnostics', []) if d['severity']=='error']
    return dict(status='verified' if v['ok'] and not v['timeout'] else 'timeout' if v['timeout'] else 'failed',
                error_kinds=dict(Counter(d['kind'] for d in errors)), diagnostics=errors[:8],
                omitted_diagnostics=max(0,len(errors)-8))


def diagnostic_experiments(source: str, observation: dict[str, Any], attempts: list[dict[str, Any]]) -> dict[str, Any]:
    data = source.encode('utf-8')
    rows = []
    for attempt in attempts:
        changes = []
        for span in attempt['removed'][:8]:
            snippet = data[span['start']:span['end']].decode('utf-8')
            changes.append(dict(kind=span['kind'], text=snippet[:400], truncated=len(snippet)>400))
        rows.append(dict(removed_annotations=changes, omitted_annotations=max(0,len(attempt['removed'])-8),
                         outcome=verification_summary(attempt)))
    return dict(original_candidate=verification_summary(observation), deletion_experiments=rows,
                interpretation='Each experiment deletes annotations from the same candidate; failed variants are not adopted. '
                'Error changes are observations, not proof progress or stable obligation identities. '
                'A disappearing diagnostic does not establish an original obligation. Timeouts are inconclusive. '
                'Original code and contracts remain frozen; the full program must verify.')
