"""Derive auditable research-only views from immutable private archives.

Nested containers are inspected and expanded, never copied opaquely. Original
archives remain unchanged. The selection ledger records every original member.
"""
from __future__ import annotations

import argparse
import contextlib
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import tarfile
import zipfile

try:
    from . import archives
except ImportError:
    try:
        import archives
    except ImportError:
        import verify_archives as archives


MAX_MEMBER = 512 * 1024 * 1024
MAX_DEPTH = 12
PRESENTATION = {'.tex', '.sty', '.bib', '.pdf', '.tikz', '.aux', '.bbl',
                '.blg', '.fls', '.fdb_latexmk', '.synctex', '.dvi'}
PRIVATE_PARTS = {'drafts', 'backups', 'recovery', '.git', '.venv',
                 '__pycache__', 'node_modules', 'site-packages'}
EDITORIAL_NAMES = {'PAPER-OUTLINE.md', 'PAPER-RELATED-WORK.md'}
SECRET_PATTERNS = (
    rb'-----BEGIN (?:RSA |OPENSSH |EC |DSA )?PRIVATE KEY-----',
    rb'\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{60,})\b',
    rb'\b(?:AKIA|ASIA)[A-Z0-9]{16}\b',
    rb'\bsk-(?:proj-)?[A-Za-z0-9_-]{40,}\b',
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def exclusion(name: str) -> str | None:
    path = PurePosixPath(name)
    parts = set(path.parts)
    if path.suffix.lower() in PRESENTATION:
        return 'manuscript-or-typeset-presentation'
    if parts & PRIVATE_PARTS or path.name == '.DS_Store':
        return 'recovery-or-installed-environment'
    if any(p.startswith(('submission-review-', 'submission-final-')) for p in path.parts):
        return 'manuscript-editorial-workspace'
    if path.name in EDITORIAL_NAMES or '/tools/submission/' in '/' + name:
        return 'manuscript-authoring-material'
    if 'paper' in path.parts:
        i = path.parts.index('paper')
        tail = path.parts[i + 1:]
        # Keep measurements, proof inputs and their licenses, not manuscript prose.
        if not tail or tail[0] not in {'evidence', 'listings'}:
            return 'manuscript-workspace'
        if path.suffix.lower() not in {'.json', '.log', '.txt', '.py', '.dfy', '.lean'} and 'LICENSE' not in path.name:
            return 'manuscript-editorial-material'
    if re.fullmatch(r'page[-_]?[0-9]+\.(png|jpg|jpeg)', path.name, re.I):
        return 'rendered-manuscript-page'
    return None


def audit_content(name: str, data: bytes) -> None:
    for pattern in SECRET_PATTERNS:
        if re.search(pattern, data):
            raise ValueError(f'Credential-pattern match requires review in {name}')
    # Check literal and JSON-escaped LaTeX without exposing matched contents.
    if (b'\\documentclass' in data and b'\\begin{document}' in data) or b'\\begin{abstract}' in data:
        raise ValueError(f'Embedded manuscript requires review in {name}')
    if data.startswith(b'%PDF-'):
        raise ValueError(f'Unexpected PDF content requires review in {name}')


def bounded_read(stream, size: int) -> bytes:
    if size > MAX_MEMBER:
        raise ValueError(f'Member exceeds inspection limit of {MAX_MEMBER} bytes')
    data = stream.read(MAX_MEMBER + 1)
    if len(data) > MAX_MEMBER:
        raise ValueError('Decompressed member exceeds inspection limit')
    return data


class ResearchView:
    def __init__(self, writer=None, replay_readme: bytes | None = None):
        self.writer = writer
        self.replay_readme = replay_readme
        self.members = {}
        self.ledger = []

    def emit(self, name: str, data: bytes, mode: int = 0o644):
        archives.safe_name(name)
        if name in self.members:
            raise ValueError(f'Public member collision: {name}')
        audit_content(name, data)
        self.members[name] = {'sha256': digest(data), 'bytes': len(data)}
        if self.writer is not None:
            info = tarfile.TarInfo(name)
            info.size, info.mode = len(data), mode & 0o777
            info.mtime = info.uid = info.gid = 0
            info.uname = info.gname = ''
            self.writer.addfile(info, io.BytesIO(data))

    def walk(self, source, chain: list[str], prefix: str = '', depth: int = 0):
        if depth > MAX_DEPTH:
            raise ValueError('Nested archive exceeds inspection depth')
        seen = set()
        source.seek(0)
        if zipfile.is_zipfile(source):
            source.seek(0)
            with zipfile.ZipFile(source) as archive:
                for entry in archive.infolist():
                    name = archives.safe_name(entry.filename)
                    if name in seen:
                        raise ValueError(f'Duplicate source member: {name}')
                    seen.add(name)
                    if entry.is_dir():
                        continue
                    with archive.open(entry) as stream:
                        data = bounded_read(stream, entry.file_size)
                    if stat.S_ISLNK(entry.external_attr >> 16):
                        self.ledger.append({'archive_chain': chain, 'member': name,
                                            'sha256': digest(data), 'bytes': len(data),
                                            'action': 'link-metadata-only',
                                            'target': data.decode(), 'type': 'zip-symlink'})
                        continue
                    self.file(name, data, chain, prefix, depth, (entry.external_attr >> 16) or 0o644)
        else:
            source.seek(0)
            with tarfile.open(fileobj=source, mode='r:*') as archive:
                for entry in archive:
                    name = archives.safe_name(entry.name)
                    if name in seen:
                        raise ValueError(f'Duplicate source member: {name}')
                    seen.add(name)
                    if entry.isdir():
                        continue
                    if entry.issym() or entry.islnk():
                        self.ledger.append({'archive_chain': chain, 'member': name,
                                            'action': 'link-metadata-only', 'target': entry.linkname,
                                            'type': entry.type.decode()})
                        continue
                    if not entry.isfile():
                        raise ValueError(f'Unsupported source entry: {name}')
                    with archive.extractfile(entry) as stream:
                        data = bounded_read(stream, entry.size)
                    self.file(name, data, chain, prefix, depth, entry.mode)

    def file(self, name, data, chain, prefix, depth, mode):
        destination = prefix + name
        record = {'archive_chain': chain, 'member': name, 'sha256': digest(data), 'bytes': len(data)}
        self.ledger.append(record)
        # Inspect containers even inside editorial packages so selection is auditable.
        stream = io.BytesIO(data)
        is_zip = zipfile.is_zipfile(stream)
        is_tar = False
        if not is_zip and (data[:2] == b'\x1f\x8b' or data[257:262] == b'ustar' or name.endswith(('.tar', '.tgz', '.tar.xz', '.tar.bz2'))):
            try:
                stream.seek(0)
                with tarfile.open(fileobj=stream, mode='r:*'):
                    is_tar = True
            except tarfile.TarError:
                pass
        if is_zip or is_tar:
            record.update(action='container-expanded', destination=destination + '.unpacked/')
            self.walk(io.BytesIO(data), chain + [name], destination + '.unpacked/', depth + 1)
            return
        reason = exclusion(destination)
        if reason:
            record.update(action='excluded', reason=reason)
            return
        if data[:2] == b'\x1f\x8b':
            with gzip.GzipFile(fileobj=io.BytesIO(data)) as compressed:
                plain = bounded_read(compressed, 0)
            reason = exclusion(destination.removesuffix('.gz'))
            if reason:
                record.update(action='excluded', reason=reason)
                return
            audit_content(destination + ' (decompressed)', plain)
            record['decompressed_sha256'] = digest(plain)
        if self.replay_readme is not None and destination == 'veripy-supplement/README.md':
            record.update(action='replaced', reason='research-only-reproduction-guide', destination=destination)
            self.emit(destination, self.replay_readme)
            return
        if self.replay_readme is not None and destination == 'veripy-supplement/MANIFEST.json':
            destination = 'veripy-supplement/provenance/original-artifact-manifest.json'
            record['action'] = 'relocated'
        else:
            record['action'] = 'included'
        record['destination'] = destination
        self.emit(destination, data, mode)
        if self.replay_readme is not None and destination == 'veripy-supplement/requirements-lock.txt':
            lines = []
            for line in data.decode().splitlines():
                if line.startswith('basedpyright=='):
                    lines.append('basedpyright==1.39.10')
                elif line.startswith('z3-solver=='):
                    lines.append(line + '; sys_platform != "darwin" or platform_machine != "arm64"')
                    lines.append('z3-solver==4.15.1.0; sys_platform == "darwin" and platform_machine == "arm64"')
                else:
                    lines.append(line)
            self.emit('veripy-supplement/requirements-replay.txt', ('\n'.join(lines) + '\n').encode())

    def finish_replay(self):
        if self.replay_readme is not None:
            prefix = 'veripy-supplement/'
            hashes = {name.removeprefix(prefix): data['sha256'] for name, data in self.members.items()}
            self.emit(prefix + 'MANIFEST.json', (json.dumps(hashes, indent=2, sort_keys=True) + '\n').encode())


def build(args):
    catalog = json.loads(args.catalog.read_text())
    source_commit = subprocess.check_output(['git', 'rev-parse', args.source_commit + '^{commit}'], text=True).strip()
    if args.out.exists():
        raise ValueError('Output already exists. Archive candidates are immutable.')
    args.out.mkdir(parents=True)
    readme = args.readme.read_bytes()
    archives_out, index, ledger, sources = [], {}, {}, []
    labels = {'case-studies': 'history', 'paper-artifact': 'replay', 'experiment-records': 'records'}
    for entry in catalog['archives']:
        path = args.assets / entry['file']
        if archives.sha256(path) != entry['sha256'] or path.stat().st_size != entry['bytes']:
            raise ValueError(f'Source archive hash/size mismatch: {path.name}')
        label = next(v for k, v in labels.items() if f'-{k}-' in path.name)
        name = f'veripy-research-{label}-{args.version}.tar.gz'
        destination = args.out / name
        with contextlib.ExitStack() as stack:
            writer = None
            if not args.audit_only:
                raw = stack.enter_context(destination.open('wb'))
                compressed = stack.enter_context(gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0))
                writer = stack.enter_context(tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT))
            view = ResearchView(writer, readme if label == 'replay' else None)
            with path.open('rb') as source:
                view.walk(source, [path.name])
            view.finish_replay()
        index[name], ledger[name] = view.members, view.ledger
        sources.append({k: entry[k] for k in ('file', 'sha256', 'bytes')})
        if not args.audit_only:
            if archives.inventory(destination) != view.members:
                raise ValueError(f'Written member inventory mismatch: {name}')
            archives_out.append({'file': name, 'sha256': archives.sha256(destination),
                                 'bytes': destination.stat().st_size, 'members': len(view.members)})
        print(f'Inspected {label}: {len(view.ledger)} source members, {len(view.members)} public files', flush=True)
    archives.gzip_json(args.out / 'SELECTION.json.gz', ledger)
    archives.gzip_json(args.out / 'FILE-INVENTORY.json.gz', index)
    if args.audit_only:
        archives.write_json(args.out / 'AUDIT.json', {'status': 'passed', 'sources': sources,
                                                    'source_commit': source_commit})
        return
    asset = lambda p: {'file': p.name, 'sha256': archives.sha256(p), 'bytes': p.stat().st_size}
    manifest = {'schema': 1, 'version': 'research-' + args.version,
                'source_commit': source_commit, 'original_archives': sources,
                'archives': archives_out, 'inventory': asset(args.out / 'FILE-INVENTORY.json.gz'),
                'attachments': [asset(args.out / 'SELECTION.json.gz')],
                'selection_policy': 'All outcomes retained. Manuscript/presentation material, editorial workspaces, recovery copies and installed environments excluded by path. Nested containers expanded. Link metadata retained without following links. Selection ledger identifies original hashes and every decision.'}
    archives.write_json(args.out / 'MANIFEST.json', manifest)
    shutil.copyfile(args.readme, args.out / 'README.md')
    shutil.copyfile(Path(archives.__file__), args.out / 'verify_archives.py')
    shutil.copyfile(Path(__file__), args.out / 'public_release.py')
    (args.out / 'SHA256SUMS').write_text(''.join(f'{archives.sha256(p)}  {p.name}\n' for p in sorted(args.out.iterdir()) if p.is_file()))
    print(json.dumps(archives.verify(args.out / 'MANIFEST.json', args.out, contents=True), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog', type=Path, required=True)
    parser.add_argument('--assets', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--version', required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--readme', type=Path, required=True)
    parser.add_argument('--audit-only', action='store_true')
    args = parser.parse_args()
    if not re.fullmatch(r'\d{4}-\d{2}-\d{2}(?:-[a-z0-9]+)?', args.version):
        parser.error('Use a dated version identifier')
    build(args)


if __name__ == '__main__':
    main()
