"""Package immutable research snapshots, or verify downloaded release assets.

Uses only the standard library. Verification never extracts or executes archives.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import tarfile
import zipfile


ROOT = Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def safe_name(name: str) -> str:
    if not name or name.startswith('/') or '..' in name.split('/') or '\\' in name:
        raise ValueError(f'Unsafe archive member or asset name {name!r}')
    return name


def inventory(path: Path) -> dict:
    """Hash every file, preserving links without following them."""
    result = {}

    def add(name, stream, size):
        safe_name(name)
        if name in result:
            raise ValueError(f'Duplicate member {name}')
        with stream:
            result[name] = {'sha256': hashlib.file_digest(stream, 'sha256').hexdigest(), 'bytes': size}

    if zipfile.is_zipfile(path):
        with zipfile.ZipFile(path) as archive:
            for member in archive.infolist():
                if not member.is_dir():
                    add(member.filename, archive.open(member), member.file_size)
    else:
        with tarfile.open(path, 'r:*') as archive:
            for member in archive:
                safe_name(member.name)
                if member.isfile():
                    add(member.name, archive.extractfile(member), member.size)
                elif member.issym() or member.islnk():
                    if member.name in result:
                        raise ValueError(f'Duplicate member {member.name}')
                    result[member.name] = {'link': member.linkname, 'type': member.type.decode()}
                elif not member.isdir():
                    raise ValueError(f'Unsupported archive entry {member.name}')
    return result


def write_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def gzip_json(path: Path, data) -> None:
    with path.open('wb') as raw, gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as stream:
        stream.write((json.dumps(data, sort_keys=True) + '\n').encode())


def collect_records(root: Path, paths: list[Path], exclusions: list[Path]) -> dict:
    result = {}
    for source in paths:
        if not source.exists():
            raise ValueError(f'Missing record source {source}')
        candidates = [source] if source.is_file() else source.rglob('*')
        for path in candidates:
            if any(path == excluded or excluded in path.parents for excluded in exclusions):
                continue
            if '__pycache__' in path.parts or path.name == '.DS_Store':
                continue
            if path.is_symlink():
                raise ValueError(f'Record sources must be files, not symbolic links {path}')
            if path.is_file():
                name = path.relative_to(root).as_posix()
                result[name] = {'sha256': sha256(path), 'bytes': path.stat().st_size}
    if not result:
        raise ValueError('No experiment records selected')
    return dict(sorted(result.items()))


def pack_records(path: Path, root: Path, records: dict) -> None:
    with path.open('wb') as raw, gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as stream:
        with tarfile.open(fileobj=stream, mode='w|', format=tarfile.PAX_FORMAT) as archive:
            for name in records:
                source = root / name
                info = archive.gettarinfo(str(source), arcname=name)
                info.uid = info.gid = info.mtime = 0
                info.uname = info.gname = ''
                info.pax_headers = {}
                with source.open('rb') as content:
                    archive.addfile(info, content)
    if inventory(path) != records:
        raise ValueError('Experiment record bytes changed while packaging')


def verify(manifest: Path, assets: Path, contents: bool = False) -> dict:
    data = json.loads(manifest.read_text())
    entries = data['archives'] + [data['inventory']] + data.get('attachments', [])
    for entry in entries:
        name = safe_name(entry['file'])
        if '/' in name:
            raise ValueError('Assets must be direct children of the asset directory')
        path = assets / name
        if not path.is_file() or path.stat().st_size != entry['bytes'] or sha256(path) != entry['sha256']:
            raise ValueError(f'Missing or changed asset {name}')
    checked = 0
    if contents:
        with gzip.open(assets / data['inventory']['file'], 'rt') as stream:
            expected = json.load(stream)
        if set(expected) != {entry['file'] for entry in data['archives']}:
            raise ValueError('Inventory archive set does not match the catalog')
        for entry in data['archives']:
            members = inventory(assets / entry['file'])
            if members != expected[entry['file']] or len(members) != entry['members']:
                raise ValueError(f'Missing, extra or changed members in {entry["file"]}')
            checked += len(members)
    return {'status': 'passed', 'version': data['version'], 'archives': len(data['archives']),
            'file_inventory_checked': contents, 'members_checked': checked}


def package(args) -> None:
    if not re.fullmatch(r'\d{4}-\d{2}-\d{2}(?:-[a-z0-9]+)?', args.version):
        raise ValueError('Use a dated version such as 2026-09-14 or 2026-09-14-r2')
    out = args.out.resolve()
    catalog = args.manifest.resolve()
    if out.exists() or catalog.exists():
        raise ValueError('Archive versions are immutable. Choose a new version and unused paths.')
    records = collect_records(ROOT, [p.resolve() for p in args.records], [p.resolve() for p in args.exclude])
    original = json.loads(args.history_files.read_text())
    out.mkdir(parents=True)
    archive_entries, file_index = [], {}
    sources = [
        ('case-studies', 'tar.gz', args.history, 'Complete original case_studies tree. All outcomes, reviews, pilots and frozen compilers are retained.'),
        ('paper-artifact', 'zip', args.paper_artifact, 'Exact frozen submission artifact, including both maintenance arms and unsuccessful outcomes. This is the starting point for paper reproduction.'),
        ('experiment-records', 'tar.gz', None, 'All selected research bundles, packaging/replay receipts and paper evidence, without outcome-based filtering.'),
    ]
    for label, extension, source, scope in sources:
        name = f'veripy-{label}-{args.version}.{extension}'
        dest = out / name
        if source is None:
            pack_records(dest, ROOT, records)
            members = records
        else:
            shutil.copyfile(source, dest)
            if sha256(source) != sha256(dest):
                raise ValueError(f'Copy changed {source}')
            members = inventory(dest)
        if label == 'case-studies':
            hashes = {name: entry['sha256'] for name, entry in members.items() if 'sha256' in entry}
            if hashes != original:
                raise ValueError('Historical archive does not preserve the complete original file manifest')
        file_index[name] = members
        archive_entries.append({'file': name, 'bytes': dest.stat().st_size, 'sha256': sha256(dest),
                                'members': len(members), 'scope': scope,
                                'source': str(source.relative_to(ROOT)) if source else 'record_selection'})
        print(f'Packaged {name} with {len(members)} members', flush=True)
    index = out / f'veripy-file-inventory-{args.version}.json.gz'
    gzip_json(index, file_index)
    data = {'schema': 1, 'version': args.version, 'publication_status': 'prepared-locally',
            'release_url': None, 'archives': archive_entries,
            'inventory': {'file': index.name, 'bytes': index.stat().st_size, 'sha256': sha256(index)},
            'record_selection': {'include': [str(p.resolve().relative_to(ROOT)) for p in args.records],
                                 'exclude': [str(p.resolve().relative_to(ROOT)) for p in args.exclude],
                                 'always_excluded': ['__pycache__ directories', '.DS_Store'],
                                 'selection_rule': 'Preserve every selected file regardless of result. Exclusions remove installed environments and duplicate extraction trees, not failed runs.'}}
    write_json(out / 'MANIFEST.json', data)
    shutil.copyfile(ROOT / 'docs/RESEARCH-ARCHIVES.md', out / 'README.md')
    shutil.copyfile(Path(__file__), out / 'verify_archives.py')
    sums = ''.join(f'{sha256(p)}  {p.name}\n' for p in sorted(out.iterdir()) if p.is_file())
    (out / 'SHA256SUMS').write_text(sums)
    catalog.parent.mkdir(parents=True, exist_ok=True)
    write_json(catalog, data)
    print(json.dumps(verify(catalog, out), indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    check = commands.add_parser('verify')
    check.add_argument('--manifest', type=Path, required=True)
    check.add_argument('--assets', type=Path, required=True)
    check.add_argument('--contents', action='store_true', help='Also hash every archived member against the complete inventory')
    build = commands.add_parser('package')
    build.add_argument('--version', required=True)
    build.add_argument('--out', type=Path, required=True)
    build.add_argument('--manifest', type=Path, required=True)
    build.add_argument('--history', type=Path, required=True)
    build.add_argument('--history-files', type=Path, required=True)
    build.add_argument('--paper-artifact', type=Path, required=True)
    build.add_argument('--records', nargs='+', type=Path, required=True)
    build.add_argument('--exclude', nargs='*', type=Path, default=[])
    args = parser.parse_args()
    try:
        if args.command == 'package':
            args.history = args.history.resolve()
            args.paper_artifact = args.paper_artifact.resolve()
            package(args)
        else:
            print(json.dumps(verify(args.manifest, args.assets, args.contents), indent=2))
    except (ValueError, OSError, tarfile.TarError, zipfile.BadZipFile) as error:
        parser.exit(1, f'Archive check failed: {error}\n')


if __name__ == '__main__':
    main()
