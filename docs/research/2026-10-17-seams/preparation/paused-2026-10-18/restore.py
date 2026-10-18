#!/usr/bin/env python3
"""Verify the frozen packet, or restore missing files without overwriting changes."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import tarfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--restore', type=Path, help='restore below this directory; the original directory is /private/tmp')
args = parser.parse_args()
base = Path(__file__).resolve().parent
manifest = json.loads((base/'manifest.json').read_text())
archive = base/manifest['archive']
assert hashlib.sha256(archive.read_bytes()).hexdigest() == manifest['archiveSha256'], 'Archive hash differs'
rows = manifest['files']
assert len(rows) == manifest['fileCount']
assert len({r['path'] for r in rows}) == len(rows), 'Duplicate manifest path'
data = {}
with tarfile.open(archive, 'r:gz') as tar:
    members = tar.getmembers()
    assert [m.name for m in members] == [r['path'] for r in rows], 'Archive inventory differs'
    for member, row in zip(members, rows):
        rel = PurePosixPath(row['path'])
        assert not rel.is_absolute() and '..' not in rel.parts and member.isfile(), row['path']
        payload = tar.extractfile(member).read()
        assert len(payload) == row['bytes'], row['path']
        assert hashlib.sha256(payload).hexdigest() == row['sha256'], row['path']
        data[row['path']] = payload
if args.restore is not None:
    destination = args.restore.resolve()
    missing = []
    for row in rows:
        target = destination/row['path']
        assert target.resolve().is_relative_to(destination), f'Path escapes destination: {target}'
        assert not target.is_symlink(), f'Symlink destination: {target}'
        if target.exists():
            assert target.is_file() and target.read_bytes() == data[row['path']], f'Existing file differs: {target}'
        else:
            missing.append((target, data[row['path']]))
    for target, payload in missing:
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(payload)
    print(json.dumps({'verifiedFiles': len(rows), 'restoredFiles': len(missing), 'destination': str(destination)}))
else:
    print(json.dumps({'verifiedFiles': len(rows), 'archiveSha256': manifest['archiveSha256'], 'mode': 'verify only'}))
