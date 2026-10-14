#!/usr/bin/env python3
"""Check finite-data identities and journal counts; use verifier/verify.py for mathematical checks."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_NAME = 'Wilf_execution_companions_v1.tar'
ARCHIVE_BYTES = 636661760
SCOPE = list(range(14, 38))
STAGES = ('profiles', 'allocations', 'tuples', 'labels')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(stream):
    h = hashlib.sha256()
    size = lines = 0
    for block in iter(lambda: stream.read(1024 * 1024), b''):
        h.update(block)
        size += len(block)
        lines += block.count(b'\n')
    return h.hexdigest(), size, lines


def file_digest(path):
    with path.open('rb') as stream:
        return digest(stream)


def read_json(path):
    return json.loads(path.read_text())


def inventory(archive, expected):
    members = archive.getmembers()
    names = [m.name for m in members]
    require(len(names) == len(set(names)), 'duplicate archive members')
    require(set(names) == set(expected), 'unexpected archive inventory')
    for m in members:
        p = PurePosixPath(m.name)
        require(m.isfile() and not p.is_absolute() and '..' not in p.parts,
                'unsafe archive member: ' + m.name)
    return members


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, help='optional ' + ARCHIVE_NAME)
    parser.add_argument('--full', action='store_true', help='also decompress all journals and check content hashes/counts')
    args = parser.parse_args()
    require(not args.full or args.archive is not None, '--full requires --archive')
    manifest_bytes = (ROOT / 'results/MANIFEST.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    require(manifest['executed_n'] == SCOPE and manifest['status'] == 'closed', 'case scope/status')
    require(manifest['cardinality_domain'] == [14, 37], 'cardinality domain')
    require(set(manifest['source_hashes']) == {'arithmetic.py', 'cover.py', 'verify.py', 'RULES.json'}, 'checker source inventory')
    for name, expected in manifest['source_hashes'].items():
        require(file_digest(ROOT / 'verifier' / name)[0] == expected, 'checker source identity: ' + name)
    index = read_json(ROOT / 'results/JOURNAL_INDEX.json')
    require(index['scope'] == SCOPE, 'journal index scope')
    streams = {row['path']: row for row in index['streams']}
    require(len(streams) == len(index['streams']) == 96, 'journal count/duplicates')
    expected_files = {'execution-v1/MANIFEST.json': manifest_bytes}
    totals = {stage: 0 for stage in STAGES}
    for n in SCOPE:
        data = (ROOT / ('results/manifests/n%d.json' % n)).read_bytes()
        require(hashlib.sha256(data).hexdigest() == manifest['manifest_hashes']['n%d' % n], 'manifest hash n%d' % n)
        case = json.loads(data)
        require(case['n'] == n and case['status'] == 'closed' and case['unresolved'] == [] and case['omitted_children'] == 0, 'manifest closure n%d' % n)
        require(set(case['stages']) == set(STAGES), 'manifest stages n%d' % n)
        expected_files['execution-v1/n%d/manifest.json' % n] = data
        for stage in STAGES:
            item = case['stages'][stage]
            require(item['file'] == stage + '.jsonl.gz', 'stage filename')
            path = 'execution-v1/n%d/%s' % (n, item['file'])
            require(path in streams, 'missing index entry ' + path)
            for key in ('sha256', 'content_sha256', 'events'):
                require(streams[path][key] == item[key], 'index/manifest mismatch ' + path + ':' + key)
            totals[stage] += item['events']
    print('PASS: checker sources, 24 case manifests and journal index.', flush=True)
    if args.archive:
        expected_sha, asset_name = (ROOT / 'results/SHA256SUMS').read_text().split()
        require(asset_name == ARCHIVE_NAME, 'archive checksum filename')
        sha, size, _ = file_digest(args.archive)
        require(sha == expected_sha and size == ARCHIVE_BYTES, 'execution archive hash/size')
        with tarfile.open(args.archive, 'r:') as archive:
            inventory(archive, set(expected_files) | set(streams))
            for name, data in expected_files.items():
                archived = archive.extractfile(name).read()
                if name == 'execution-v1/MANIFEST.json':
                    require(json.loads(archived) == manifest, 'archived input manifest differs')
                else:
                    require(archived == data, 'archived case manifest differs: ' + name)
            for n in SCOPE:
                for stage in STAGES:
                    name = 'execution-v1/n%d/%s.jsonl.gz' % (n, stage)
                    expected = streams[name]
                    with archive.extractfile(name) as stream:
                        sha, size, _ = digest(stream)
                    require(sha == expected['sha256'] and size == expected['bytes'], 'compressed journal mismatch: ' + name)
                    if args.full:
                        with archive.extractfile(name) as compressed:
                            with gzip.GzipFile(fileobj=compressed) as stream:
                                sha, _, lines = digest(stream)
                        require(sha == expected['content_sha256'] and lines == expected['events'], 'journal content/count mismatch: ' + name)
                print('PASS: n%d compressed journals%s' % (n, ' and decompressed content/counts' if args.full else ''), flush=True)
        print('PASS: execution archive inventory, metadata and all 96 journals.', flush=True)
    print(json.dumps({'declared_events': totals, 'full_decompressed_check': args.full,
                      'mathematical_verification': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration, tarfile.TarError, EOFError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
