"""Check rendered local links, assets and anchors under the GitHub Pages base."""
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit, unquote, urljoin

ROOT = Path(__file__).resolve().parents[1] / 'dist'
class Page(HTMLParser):
    def __init__(self, text):
        super().__init__(); self.ids=set(); self.links=[]; self.feed(text)
    def handle_starttag(self, tag, attrs):
        attrs=dict(attrs)
        if 'id' in attrs: self.ids.add(attrs['id'])
        for key in ('href','src'):
            if key in attrs: self.links.append(attrs[key])
pages={p:Page(p.read_text()) for p in ROOT.rglob('*.html')}
errors=[]
for path,page in pages.items():
    route='/veripy/'+path.relative_to(ROOT).as_posix().removesuffix('index.html')
    for href in page.links:
        url=urlsplit(urljoin('https://astrio-labs.github.io'+route,href))
        if path.name == '404.html' and url.path == '/veripy/404/':continue
        if url.netloc!='astrio-labs.github.io' or url.scheme not in ('http','https'):continue
        if not url.path.startswith('/veripy/'):
            errors.append(f'{path}: link escapes project base {href}');continue
        target=ROOT/unquote(url.path.removeprefix('/veripy/'))
        if target.is_dir():target=target/'index.html'
        if not target.exists():errors.append(f'{path}: missing {href}')
        elif url.fragment and target in pages and unquote(url.fragment) not in pages[target].ids:
            errors.append(f'{path}: missing anchor {href}')
if errors:raise SystemExit('\n'.join(errors))
print(f'Checked local links and anchors in {len(pages)} rendered pages')
