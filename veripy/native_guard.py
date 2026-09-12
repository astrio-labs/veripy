"""Insertion-only proof guard with ambiguity-aware original-token alignment.

Repeated tokens inside added proof annotations must not consume a required
original token prematurely. Keep all feasible alignment positions; non-proof
tokens may only match the original stream. This is a conservative token policy,
not a general semantic-equivalence checker.
"""
from collections import Counter


def insertion_guard(original_tokens, candidate_ast):
    if not candidate_ast.get('parse_ok'):
        return {'ok':False,'reason':'Candidate does not parse.'}
    names=set(original_tokens);states={0}
    for token in candidate_ast['tokens']:
        value=token['value']
        allowed=any(s['kind']!='lemma' or s['name'] not in names for s in token['proof'])
        matched={i+1 for i in states if i<len(original_tokens) and original_tokens[i]==value}
        states=states|matched if allowed else matched
        if not states:
            return {'ok':False,'reason':'Original token stream cannot be retained with proof-only insertions.'}
    if len(original_tokens) not in states:
        return {'ok':False,'reason':'Original tokens deleted or rewritten.'}
    values=[t['value'] for t in candidate_ast['tokens']]
    counts=Counter(values)-Counter(original_tokens)
    forbidden={'assume','expect','axiom','extern','include','refines','reveal','opaque','function','predicate','method','constructor'}
    if any(counts[x] for x in forbidden):
        return {'ok':False,'reason':'Added forbidden bypass or declaration tokens: '+str(sorted(x for x in forbidden if counts[x]))}
    for pattern in [('decreases','*'),('{',':'),('{:',)]:
        def count(ts):return sum(tuple(ts[i:i+len(pattern)])==pattern for i in range(len(ts)))
        if count(values)>count(original_tokens):
            return {'ok':False,'reason':'New attributes or nontermination escapes are forbidden.'}
    return {'ok':True,'reason':'Original tokens retained under ambiguity-aware proof-only alignment.',
            'added_token_count':len(values)-len(original_tokens)}
