"""Rebuild proof-only edit plans against immutable native source anchors.

Anchor offsets must come from the trusted parser for the original source. This
compiler preserves original bytes but does not establish semantic preservation:
its output MUST still pass the native parser, insertion/bypass guards and prover.
"""
from __future__ import annotations

import hashlib
import re
from typing import Any


class EditPlanError(ValueError):
    pass


def source_hash(source: str) -> str:
    return hashlib.sha256(source.encode('utf-8')).hexdigest()


def anchor_catalog(source: str, parser_anchors: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    data = source.encode('utf-8')
    counts = {'statement': 0, 'loop': 0, 'block_end': 0, 'expression': 0, 'declaration': 0}
    catalog = {}
    for a in sorted(parser_anchors, key=lambda a: (a['start'], a['kind'])):
        kind = a['kind']
        if kind not in counts:
            continue
        offset = a['offset']
        if type(offset) is not int or not 0 <= offset <= len(data):
            raise EditPlanError('Invalid parser anchor offset')
        counts[kind] += 1
        ident = {'statement':'S','loop':'L','block_end':'B','expression':'E','declaration':'D'}[kind]+str(counts[kind])
        line = data[:a['start']].decode('utf-8').count('\n')+1
        catalog[ident] = dict(kind=kind, offset=offset, line=line,
                              context=source.splitlines()[line-1][:240])
    catalog['END'] = dict(kind='end', offset=len(data), line=len(source.splitlines()), context='end of original file')
    return catalog


def compile_plan(original: str, catalog: dict[str, dict[str, Any]], plan: Any) -> str:
    if not isinstance(plan, dict) or set(plan) != {'original_sha256', 'edits'}:
        raise EditPlanError('Expected an object with original_sha256 and edits only')
    if plan['original_sha256'] != source_hash(original):
        raise EditPlanError('Stale or incorrect original_sha256')
    edits = plan['edits']
    if not isinstance(edits, list) or len(edits) > 32:
        raise EditPlanError('edits must be a list of at most 32 complete annotations')
    specs = {'assert_before': ('statement', 'assert'), 'loop_invariant': ('loop', 'invariant'),
             'loop_decreases': ('loop', 'decreases'), 'helper_lemma': ('end', 'lemma'), 'assert_block_end': ('block_end', 'assert'),
             'assert_expression': ('expression', 'assert'), 'declaration_decreases': ('declaration', 'decreases')}
    by_offset: dict[int, list[str]] = {}
    seen = set(); total = 0
    for edit in edits:
        if not isinstance(edit, dict) or set(edit) != {'id', 'op', 'target', 'text'}:
            raise EditPlanError('Each edit needs exactly id, op, target, text')
        ident, op, target, text = (edit[k] for k in ['id', 'op', 'target', 'text'])
        if not all(isinstance(x, str) for x in [ident, op, target, text]):
            raise EditPlanError('Edit fields must be strings')
        if not re.fullmatch(r'A[0-9]{1,3}', ident) or ident in seen:
            raise EditPlanError('Edit IDs must be unique A<number> identifiers')
        seen.add(ident)
        if op not in specs or target not in catalog:
            raise EditPlanError('Unknown edit operation or original-source target')
        kind, keyword = specs[op]
        if catalog[target]['kind'] != kind:
            raise EditPlanError(f'{op} cannot target {target}')
        text = text.strip()
        if not re.match(r'^'+keyword+r'\b', text):
            raise EditPlanError(f'{op} text must start with {keyword}')
        total += len(text)
        if len(text) > 8000 or total > 32000:
            raise EditPlanError('Annotation text exceeds the configured size cap')
        by_offset.setdefault(catalog[target]['offset'], []).append(text)
    data = original.encode('utf-8')
    for offset in sorted(by_offset, reverse=True):
        insertion = ('\n'+'\n'.join(by_offset[offset])+'\n').encode('utf-8')
        data = data[:offset]+insertion+data[offset:]
    return data.decode('utf-8')
