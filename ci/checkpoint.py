#!/usr/bin/env python3
"""Bind portable build checkpoints and exports to unchanged Lean sources."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {'.lake', '.git', '__pycache__'}


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def fingerprint():
    value = hashlib.sha256()
    for project in ['lean', 'leanWithoutComparator']:
        base = ROOT / project
        sources = [p for p in base.rglob('*.lean') if not IGNORED.intersection(p.relative_to(base).parts)]
        sources += [base / name for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]
        if project == 'lean':
            sources.append(base / 'comparator.json')
        for path in sorted(sources):
            value.update(str(path.relative_to(ROOT)).encode())
            value.update(b'\0')
            value.update(path.read_bytes())
            value.update(b'\0')
    return value.hexdigest()


def metadata():
    return {'source_fingerprint': fingerprint(),
            'toolchain': (ROOT / 'lean/lean-toolchain').read_text().strip(),
            'comparator_config_sha256': digest(ROOT / 'lean/comparator.json'),
            'commit': os.environ.get('GITHUB_SHA'),
            'run_id': os.environ.get('GITHUB_RUN_ID'),
            'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT')}


def verify_meta(record):
    expected = metadata()
    for key in ['source_fingerprint', 'toolchain', 'comparator_config_sha256']:
        if record[key] != expected[key]:
            raise SystemExit('Checkpoint/export mismatch: ' + key)


parser = argparse.ArgumentParser(description=__doc__)
sub = parser.add_subparsers(dest='command', required=True)
sub.add_parser('fingerprint')
pack = sub.add_parser('pack')
pack.add_argument('project', choices=['lean', 'leanWithoutComparator'])
pack.add_argument('directory', type=Path)
restore = sub.add_parser('restore')
restore.add_argument('project', choices=['lean', 'leanWithoutComparator'])
restore.add_argument('directory', type=Path)
exports = sub.add_parser('exports')
exports.add_argument('directory', type=Path)
verify = sub.add_parser('verify-exports')
verify.add_argument('directory', type=Path)
args = parser.parse_args()

if args.command == 'fingerprint':
    print(fingerprint())
elif args.command == 'pack':
    args.directory.mkdir(parents=True, exist_ok=True)
    archive = args.directory / 'build.tar.gz'
    with tarfile.open(archive, 'w:gz', compresslevel=1) as output:
        output.add(ROOT / args.project / '.lake/build', arcname='.lake/build')
    record = {**metadata(), 'built_in_project': args.project,
              'archive_sha256': digest(archive), 'archive_bytes': archive.stat().st_size}
    (args.directory / 'build.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))
elif args.command == 'restore':
    record = json.loads((args.directory / 'build.json').read_text())
    verify_meta(record)
    archive = args.directory / 'build.tar.gz'
    if digest(archive) != record['archive_sha256']:
        raise SystemExit('Build archive checksum mismatch')
    # Inspect the archive before extraction; only build outputs may be restored.
    with tarfile.open(archive, 'r:gz') as saved:
        for member in saved.getmembers():
            parts = Path(member.name).parts
            if (not parts or parts[:2] != ('.lake', 'build') or '..' in parts
                    or not (member.isfile() or member.isdir())):
                raise SystemExit('Unexpected build archive member: ' + member.name)
        (ROOT / args.project / '.lake').mkdir(exist_ok=True)
        saved.extractall(ROOT / args.project)
    print(json.dumps({'restored_to': args.project, 'source_fingerprint': record['source_fingerprint']}))
elif args.command == 'exports':
    args.directory.mkdir(parents=True, exist_ok=True)
    record = metadata()
    record['exports'] = {}
    record['targets'] = json.loads((ROOT / 'lean/comparator.json').read_text())['theorem_names']
    for name in ['challenge', 'solution']:
        source = ROOT / 'lean/.lake/exports' / (name + '-comparator.ndjson')
        compressed = args.directory / (name + '-comparator.ndjson.gz')
        with source.open('rb') as stream, gzip.open(compressed, 'wb', compresslevel=1) as zipped:
            shutil.copyfileobj(stream, zipped, length=8 * 1024 * 1024)
        record['exports'][name] = {'sha256': digest(source), 'bytes': source.stat().st_size,
                                  'compressed_sha256': digest(compressed)}
    (args.directory / 'exports.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))
elif args.command == 'verify-exports':
    record = json.loads((args.directory / 'exports.json').read_text())
    verify_meta(record)
    expected = json.loads((ROOT / 'lean/comparator.json').read_text())['theorem_names']
    if record['targets'] != expected:
        raise SystemExit('Wrong comparison targets')
    output = ROOT / 'lean/.lake/exports'
    output.mkdir(parents=True, exist_ok=True)
    for name, checks in record['exports'].items():
        if name not in ['challenge', 'solution']:
            raise SystemExit('Unexpected export name')
        compressed = args.directory / (name + '-comparator.ndjson.gz')
        if digest(compressed) != checks['compressed_sha256']:
            raise SystemExit('Compressed export checksum mismatch')
        dest = output / (name + '-comparator.ndjson')
        with gzip.open(compressed, 'rb') as zipped, dest.open('wb') as stream:
            shutil.copyfileobj(zipped, stream, length=8 * 1024 * 1024)
        if digest(dest) != checks['sha256'] or dest.stat().st_size != checks['bytes']:
            raise SystemExit('Uncompressed export checksum mismatch')
    if set(record['exports']) != {'challenge', 'solution'}:
        raise SystemExit('Both exports are required')
    print(json.dumps({'exports_verified': True, 'source_fingerprint': record['source_fingerprint']}))
