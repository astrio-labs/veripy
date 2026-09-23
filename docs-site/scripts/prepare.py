"""Build site pages from the repository's canonical Markdown, without duplication."""
import json
from pathlib import Path
import re
import shutil
from urllib.parse import urlsplit, unquote

ROOT = Path(__file__).resolve().parents[2]
SITE = ROOT / 'docs-site'
DEST = SITE / 'src/content/docs'
PAGES = {p: 'reference/' + p.stem.lower() for p in (ROOT / 'docs').glob('*.md') if p.name != 'README.md'}
PAGES.update({p: ('index' if p.stem == 'overview' else 'guide/' + p.stem) for p in (ROOT / 'docs/guide').glob('*.md')})

def convert_link(match, source):
    label, href = match.groups()
    parsed = urlsplit(href)
    if parsed.scheme or parsed.netloc or not parsed.path or href.startswith('/veripy/'):
        return match.group(0)
    target = (source.parent / unquote(parsed.path)).resolve()
    if not target.exists():
        raise ValueError(f'{source}: missing link {href}')
    if target in PAGES:
        slug = PAGES[target]
        url = '/veripy/' + ('' if slug == 'index' else slug + '/')
    elif target == ROOT / 'docs/README.md':
        url = '/veripy/'
    elif target.is_relative_to(ROOT / 'docs/assets') and target.suffix in ('.png', '.svg'):
        url = '/veripy/assets/' + target.name
    else:
        url = 'https://github.com/astrio-labs/veripy/blob/main/' + target.relative_to(ROOT).as_posix()
    if parsed.fragment:
        url += '#' + parsed.fragment
    return f']({url})'

shutil.rmtree(DEST, ignore_errors=True)
DEST.mkdir(parents=True)
for source, slug in PAGES.items():
    text = source.read_text()
    title, body = text.split('\n', 1)
    assert title.startswith('# '), source
    # Rewrite Markdown destinations only, leaving code examples intact.
    pieces = re.split(r'(^```[^\n]*\n.*?^```\s*$)', body, flags=re.M | re.S)
    for i in range(0, len(pieces), 2):
        pieces[i] = re.sub(r'\](\(([^)]+)\))', lambda m: convert_link(m, source), pieces[i])
    metadata = {'title': title[2:], 'editUrl': 'https://github.com/astrio-labs/veripy/edit/main/' + source.relative_to(ROOT).as_posix()}
    output = DEST / (slug + '.md')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('---\n' + '\n'.join(f'{k}: {json.dumps(v)}' for k,v in metadata.items()) + '\n---\n' + ''.join(pieces))
assets = SITE / 'public/assets'
assets.mkdir(parents=True, exist_ok=True)
shutil.copy2(ROOT / 'docs/assets/veripy-workflow.png', assets / 'veripy-workflow.png')
print(f'Prepared {len(PAGES)} documentation pages')
