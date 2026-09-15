"""Apply manuscript punctuation conventions to generated table prose only."""
import re


def clean_prose(text):
    replacements = {
        'Py: Python LOC': 'Py denotes Python LOC',
        'Spec: contract LOC': 'Spec denotes contract LOC',
        'Hint: inline proof-hint LOC': 'Hint denotes inline proof-hint LOC',
        'Final failure: ': 'Failure from ',
        'definitions equally: both arms': 'definitions equally. Both arms',
    }
    for name in ('Black', 'SGLang', 'PyTorch', 'Django', 'vLLM', 'CPython', 'Luhn'):
        replacements[name + ': '] = name + ' '
    for old, new in replacements.items():
        text = text.replace(old, new)
    text = re.sub(r'(?<!\\);(\s*)([a-z])',
                  lambda m: '.' + m[1] + m[2].upper(), text)
    return re.sub(r'(?<!\\);', '.', text)
