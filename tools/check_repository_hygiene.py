"""Reject generated files and large experiment blobs in the Git index."""
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
LIMIT = 10 * 1024 * 1024
GENERATED = [
    'output/probe.json', 'tmp/probe.py', 'tests/__pycache__/probe.pyc',
    '.pytest_cache/probe', '.mypy_cache/probe', '.ruff_cache/probe',
    '.cache/probe', '.hypothesis/probe', '.crosshair/probe', '.lake/build/probe',
    '.venv/probe', '.tox/probe', '.nox/probe', 'build/probe', 'dist/probe',
    '.coverage', 'paper/probe.aux', 'paper/probe.bbl', 'paper/probe.blg',
    'paper/probe.fdb_latexmk', 'paper/probe.fls', 'paper/probe.log',
    'paper/probe.out', 'paper/probe.synctex.gz', 'paper/probe.toc',
    'paper/probe.bcf', 'paper/probe.run.xml', 'paper/probe.nav',
    'paper/probe.snm', 'paper/probe.vrb', 'paper/probe.xdv',
    'paper/probe.idx', 'paper/probe.ind', 'paper/probe.ilg',
    'paper/evidence/layout-render-01/page.png',
]


def git(*args, input=None):
    return subprocess.run(['git', *args], cwd=ROOT, input=input, capture_output=True, check=False)


def main() -> int:
    ignored = git('ls-files', '-ci', '--exclude-standard', '-z')
    tracked = git('ls-files', '-s', '-z')
    if ignored.returncode or tracked.returncode:
        raise RuntimeError('Cannot inspect the Git index')
    errors = [f'Generated or ignored file is tracked: {p.decode()}' for p in ignored.stdout.split(b'\0') if p]
    matched = git('check-ignore', '--no-index', '--stdin', '-z', input='\0'.join(GENERATED).encode() + b'\0')
    if matched.returncode not in (0, 1):
        raise RuntimeError('Cannot inspect Git ignore rules')
    missing = set(GENERATED) - {p.decode() for p in matched.stdout.split(b'\0') if p}
    errors.extend(f'Ignore rule missing: {p}' for p in sorted(missing))
    # Read indexed blob sizes, so an oversized staged file cannot be hidden by
    # replacing or removing its working copy before this check.
    entries = [line.split(b'\t', 1) for line in tracked.stdout.split(b'\0') if line]
    regular = [(meta.split()[1], name) for meta, name in entries if meta.split()[0] != b'160000']
    if regular:
        sizes = git('cat-file', '--batch-check=%(objectsize)', input=b'\n'.join(oid for oid, _ in regular) + b'\n')
        if sizes.returncode:
            raise RuntimeError('Cannot inspect indexed blob sizes')
        values = sizes.stdout.splitlines()
        if len(values) != len(regular):
            raise RuntimeError('Incomplete indexed blob size response')
        for (_, name), size in zip(regular, values):
            if int(size) > LIMIT:
                errors.append(f'File exceeds 10 MiB; use a research archive attachment: {name.decode()}')
    for error in errors:
        print(error)
    if not errors:
        print('Repository hygiene passed. No ignored files or blobs over 10 MiB are tracked.')
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
