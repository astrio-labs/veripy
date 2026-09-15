import io
import json
import subprocess
import tarfile

import pytest

from tools.research import archives
from tools import check_repository_hygiene as hygiene


def write_tar(path, records):
    with tarfile.open(path, 'w:gz') as archive:
        for name, content in records:
            info = tarfile.TarInfo(name)
            info.size = len(content)
            archive.addfile(info, io.BytesIO(content))


@pytest.fixture
def bundle(tmp_path):
    asset = tmp_path / 'records.tar.gz'
    write_tar(asset, [('run/success.json', b'{"status":"proved"}'),
                      ('run/failure.json', b'{"status":"budget-exhausted"}')])
    index = tmp_path / 'inventory.json.gz'
    archives.gzip_json(index, {asset.name: archives.inventory(asset)})
    entry = lambda p: {'file': p.name, 'bytes': p.stat().st_size, 'sha256': archives.sha256(p)}
    data = {'version': 'test', 'archives': [{**entry(asset), 'members': 2}], 'inventory': entry(index)}
    manifest = tmp_path / 'MANIFEST.json'
    archives.write_json(manifest, data)
    return tmp_path, manifest, asset


def test_verifier_checks_success_and_failure_without_source_checkout(bundle):
    root, manifest, _ = bundle
    assert archives.verify(manifest, root, contents=True)['members_checked'] == 2


def test_removed_failure_is_detected_even_if_outer_archive_checksum_is_updated(bundle):
    root, manifest, asset = bundle
    write_tar(asset, [('run/success.json', b'{"status":"proved"}')])
    data = json.loads(manifest.read_text())
    data['archives'][0].update(bytes=asset.stat().st_size, sha256=archives.sha256(asset))
    archives.write_json(manifest, data)
    with pytest.raises(ValueError, match='Missing, extra or changed members'):
        archives.verify(manifest, root, contents=True)


@pytest.mark.parametrize('missing', [False, True])
def test_asset_corruption_or_loss_fails(bundle, missing):
    root, manifest, asset = bundle
    if missing:
        asset.unlink()
    else:
        asset.write_bytes(b'changed experiment')
    with pytest.raises(ValueError, match='Missing or changed asset'):
        archives.verify(manifest, root)


def test_duplicate_archive_members_are_rejected(tmp_path):
    path = tmp_path / 'duplicate.tar.gz'
    write_tar(path, [('result.json', b'failed'), ('result.json', b'proved')])
    with pytest.raises(ValueError, match='Duplicate member'):
        archives.inventory(path)


def test_recovery_mapping_is_bound_by_catalog_checksum(bundle):
    root, manifest, _ = bundle
    mapping = root / 'recovery.json'
    mapping.write_text('{"failed-run":"retained"}')
    data = json.loads(manifest.read_text())
    data['attachments'] = [{'file': mapping.name, 'bytes': mapping.stat().st_size,
                            'sha256': archives.sha256(mapping)}]
    archives.write_json(manifest, data)
    assert archives.verify(manifest, root)['status'] == 'passed'
    mapping.write_text('{"failed-run":"omitted"}')
    with pytest.raises(ValueError, match='Missing or changed asset recovery.json'):
        archives.verify(manifest, root)


def test_record_packaging_is_lossless_and_deterministic(tmp_path):
    records = tmp_path / 'records'
    records.mkdir()
    (records / 'failure.log').write_text('timeout\n')
    (records / 'success.json').write_text('{"status":"proved"}\n')
    expected = archives.collect_records(tmp_path, [records], [])
    first, second = tmp_path / 'first.tar.gz', tmp_path / 'second.tar.gz'
    archives.pack_records(first, tmp_path, expected)
    archives.pack_records(second, tmp_path, expected)
    assert first.read_bytes() == second.read_bytes()
    assert set(archives.inventory(first)) == {'records/failure.log', 'records/success.json'}


@pytest.fixture
def git_repo(tmp_path, monkeypatch):
    original = hygiene.ROOT
    subprocess.run(['git', 'init', '-q', str(tmp_path)], check=True)
    (tmp_path / '.gitignore').write_bytes((original / '.gitignore').read_bytes())
    monkeypatch.setattr(hygiene, 'ROOT', tmp_path)
    return tmp_path


def test_hygiene_rejects_force_added_generated_record(git_repo, capsys):
    assert hygiene.main() == 0
    path = git_repo / 'output/failure.json'
    path.parent.mkdir()
    path.write_text('{"status":"failed"}')
    subprocess.run(['git', 'add', '-f', 'output/failure.json'], cwd=git_repo, check=True)
    assert hygiene.main() == 1
    assert 'Generated or ignored file is tracked: output/failure.json' in capsys.readouterr().out


def test_hygiene_checks_large_staged_blob_even_after_working_copy_removed(git_repo, capsys):
    path = git_repo / 'experiment.data'
    path.write_bytes(b'x' * (hygiene.LIMIT + 1))
    subprocess.run(['git', 'add', 'experiment.data'], cwd=git_repo, check=True)
    path.unlink()
    assert hygiene.main() == 1
    assert 'File exceeds 10 MiB' in capsys.readouterr().out


def test_source_and_compact_evidence_remain_visible(git_repo):
    for name in ['docs/assets/veripy-workflow.pdf', 'docs/assets/veripy-workflow.png', 'case_studies/black/mapping.proofs.dfy',
                 'case_studies/evidence/functional-portfolio.json', 'docs/research-archives/2026-09-14.json']:
        result = subprocess.run(['git', 'check-ignore', '--no-index', name], cwd=git_repo, capture_output=True)
        assert result.returncode == 1, name
    for name in ['paper/neurips_2026_vericode_workshop.tex', 'paper/figures/workflow.pdf']:
        result = subprocess.run(['git', 'check-ignore', '--no-index', name], cwd=git_repo, capture_output=True)
        assert result.returncode == 0, name
