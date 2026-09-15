import gzip
import io
import json
import tarfile
import zipfile

import pytest

from tools.research.public_release import ResearchView, exclusion


def zip_bytes(items):
    target = io.BytesIO()
    with zipfile.ZipFile(target, 'w') as archive:
        for name, value in items:
            archive.writestr(name, value)
    return target.getvalue()


def view(items):
    result = ResearchView()
    result.walk(io.BytesIO(zip_bytes(items)), ['original.zip'])
    return result


def test_nested_manuscript_removed_without_losing_failed_trial():
    nested = zip_bytes([('run/success.json', b'{"status":"proved"}'),
                        ('run/failure.json', b'{"status":"budget-exhausted"}'),
                        ('paper/main.tex', b'private manuscript'),
                        ('review-01/REVIEW.md', b'requirements rejected')])
    result = view([('history.zip', nested)])
    assert set(result.members) == {'history.zip.unpacked/run/success.json',
                                   'history.zip.unpacked/run/failure.json',
                                   'history.zip.unpacked/review-01/REVIEW.md'}
    assert len(result.ledger) == 5
    assert next(r for r in result.ledger if r['member'] == 'paper/main.tex')['action'] == 'excluded'
    assert next(r for r in result.ledger if r['member'] == 'run/failure.json')['action'] == 'included'


def test_presentation_copies_excluded_but_raw_evidence_and_licenses_kept():
    assert exclusion('paper/evidence/failed-proof.log') is None
    assert exclusion('paper/listings/DJANGO-LICENSE') is None
    assert exclusion('paper/listings/old.py') is None
    assert exclusion('paper/sections/introduction.md')
    assert exclusion('paper/evidence/submission-review-20260914/render/page-01.png')
    assert exclusion('docs/PAPER-OUTLINE.md')
    assert exclusion('case_studies/review-01/REVIEW-NOTES-01.md') is None


@pytest.mark.parametrize('member', ['../outside', '/absolute', 'a/../../outside'])
def test_unsafe_nested_paths_rejected(member):
    with pytest.raises(ValueError, match='Unsafe archive member'):
        view([('nested.zip', zip_bytes([(member, b'data')]))])


def test_duplicate_original_members_rejected():
    with pytest.warns(UserWarning, match='Duplicate name'):
        data = zip_bytes([('outcome.json', b'failed'), ('outcome.json', b'passed')])
    with pytest.raises(ValueError, match='Duplicate source member'):
        ResearchView().walk(io.BytesIO(data), ['source.zip'])


def test_expansion_collision_rejected():
    with pytest.raises(ValueError, match='Public member collision'):
        view([('nested.zip', zip_bytes([('run.json', b'failed')])),
              ('nested.zip.unpacked/run.json', b'passed')])


def test_credential_content_fails_without_echoing_the_value():
    token = b'ghp_' + b'a' * 40
    with pytest.raises(ValueError, match='Credential-pattern') as caught:
        view([('run.log', token)])
    assert token.decode() not in str(caught.value)


def test_gzip_records_inspected_and_preserved_byte_for_byte():
    data = gzip.compress(b'{"status":"failed"}', mtime=0)
    result = view([('results.json.gz', data)])
    assert result.members['results.json.gz']['bytes'] == len(data)
    assert 'decompressed_sha256' in result.ledger[0]
    with pytest.raises(ValueError, match='Embedded manuscript'):
        view([('hidden.txt.gz', gzip.compress(b'\\begin{abstract}private'))])


def test_links_recorded_without_following_them():
    data = io.BytesIO()
    with tarfile.open(fileobj=data, mode='w') as archive:
        link = tarfile.TarInfo('link')
        link.type, link.linkname = tarfile.SYMTYPE, '/private/unrelated'
        archive.addfile(link)
    result = ResearchView()
    result.walk(io.BytesIO(data.getvalue()), ['source.tar'])
    assert result.members == {}
    assert result.ledger[0]['target'] == '/private/unrelated'
    assert result.ledger[0]['action'] == 'link-metadata-only'


def test_replay_manifest_rebuilt_and_original_manifest_retained():
    original = json.dumps({'README.md': 'original-hash'}).encode()
    result = ResearchView(replay_readme=b'Research replay instructions\n')
    result.walk(io.BytesIO(zip_bytes([
        ('veripy-supplement/README.md', b'editorial notes'),
        ('veripy-supplement/MANIFEST.json', original),
        ('veripy-supplement/requirements-lock.txt', b'pytest==8.0\n'),
    ])), ['original.zip'])
    result.finish_replay()
    assert 'veripy-supplement/provenance/original-artifact-manifest.json' in result.members
    assert 'veripy-supplement/MANIFEST.json' in result.members
    assert len(result.members) == 5
