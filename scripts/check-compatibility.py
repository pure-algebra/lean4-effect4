#!/usr/bin/env python3
"""Extract frozen metadata, or compare a reviewed snapshot without rewriting it.

`prepare` and `reflect` operate only in a separate temporary checkout. `reflect`
runs Lake: hold the repository's one-Lean lane before invoking it. `promote`
creates a new supplement directory and refuses to overwrite any existing one.
The original baseline is never a destination of any command.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent / 'lib'))
import compatibility as c


def load(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    Path(path).write_text(c.canonical(value))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    prepare = sub.add_parser('prepare')
    prepare.add_argument('--work', required=True, type=Path)
    prepare.add_argument('--revision', default=c.BASE)
    prepare.add_argument('--working-tree', action='store_true', help='capture current source bytes for a candidate; cannot promote')
    reflect = sub.add_parser('reflect')
    reflect.add_argument('--work', required=True, type=Path)
    promote = sub.add_parser('promote')
    promote.add_argument('--work', required=True, type=Path)
    promote.add_argument('--destination', required=True, type=Path)
    check = sub.add_parser('compare')
    check.add_argument('--baseline', required=True, type=Path)
    check.add_argument('--candidate', required=True, type=Path)
    check.add_argument('--policy', type=Path)
    check.add_argument('--out', type=Path)
    observations = sub.add_parser('compare-observations')
    observations.add_argument('--dimension', required=True, choices=['admission', 'execution_permission'])
    observations.add_argument('--before', required=True, type=Path)
    observations.add_argument('--after', required=True, type=Path)
    observations.add_argument('--expected', required=True, type=Path)
    observations.add_argument('--out', type=Path)
    args = p.parse_args()

    inventory_path = c.ROOT / 'Test/fixtures/baseline/66ee4657/families.json'
    if args.command == 'prepare':
        revision = c.resolve_revision(c.ROOT, 'HEAD' if args.working_tree else args.revision)
        if args.work.exists():
            raise ValueError('prepare requires a nonexistent temporary checkout')
        if args.work.resolve().is_relative_to(c.ROOT):
            raise ValueError('prepare must use a checkout outside the working repository')
        read = ((lambda path: (c.ROOT / path).read_bytes()) if args.working_tree
                else (lambda path: c.git_bytes(c.ROOT, revision, path)))
        closure = c.source_closure(read)
        args.work.mkdir(parents=True)
        paths = sorted(set([x['path'] for x in closure] + c.BUILD_INPUTS + c.LAYOUT_INPUTS))
        captured = []
        for path in paths:
            target = args.work / path
            target.parent.mkdir(parents=True, exist_ok=True)
            data = read(path)
            target.write_bytes(data)
            captured.append({'path': path, 'sha256': c.digest(data)})
        if any(c.digest(read(row['path'])) != row['sha256'] for row in captured):
            raise ValueError('source changed during capture; prepare a new checkout')
        (args.work / '.lake').mkdir()
        (args.work / '.lake/packages').symlink_to(c.ROOT / '.lake/packages', target_is_directory=True)
        shutil.copyfile(inventory_path, args.work / 'inventory.json')
        shutil.copyfile(c.ROOT / 'tools/Compatibility/Extract.lean', args.work / 'Extract.lean')
        write(args.work / 'source.json', {'revision': revision, 'origin': 'working-tree' if args.working_tree else 'git',
                                         'captured_inputs': captured, 'source_closure': closure,
                                         'inventory_sha256': c.digest(inventory_path.read_bytes()),
                                         'extractor_sha256': c.digest((args.work / 'Extract.lean').read_bytes())})
        print(f'prepared {"working-tree capture" if args.working_tree else revision}: {len(closure)} modules in {args.work}')
    elif args.command == 'reflect':
        source = load(args.work / 'source.json')
        candidate = source.get('origin') == 'working-tree'
        read = ((lambda path: (args.work / path).read_bytes()) if candidate
                else (lambda path: c.git_bytes(c.ROOT, source['revision'], path)))
        for row in source.get('captured_inputs', []):
            if c.digest((args.work / row['path']).read_bytes()) != row['sha256']:
                raise ValueError('captured source changed: ' + row['path'])
        if source['source_closure'] != c.source_closure(read):
            raise ValueError('frozen closure manifest differs')
        for row in source['source_closure']:
            if c.digest((args.work / row['path']).read_bytes()) != row['sha256']:
                raise ValueError('frozen source changed: ' + row['path'])
        for path in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            if (args.work / path).read_bytes() != read(path):
                raise ValueError('frozen build metadata changed: ' + path)
        if c.digest((args.work / 'inventory.json').read_bytes()) != source['inventory_sha256']:
            raise ValueError('frozen inventory changed')
        if c.digest((args.work / 'Extract.lean').read_bytes()) != source['extractor_sha256']:
            raise ValueError('frozen extractor changed; prepare a new checkout')
        commands = [
            ['lake', 'build', *c.IMPORTS],
            ['lake', 'env', 'lean', '-M4096', '--run', 'Extract.lean', 'inventory.json', 'reflection.json'],
        ]
        for i, command in enumerate(commands):
            with (args.work / f'command-{i}.log').open('w') as log:
                result = subprocess.run(command, cwd=args.work, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                raise ValueError(f'{command}: exit {result.returncode}; see command-{i}.log')
        reflection = load(args.work / 'reflection.json')
        receipt = {'revision': source['revision'], 'toolchain': read('lean-toolchain').decode().strip(),
                   'source_closure': source['source_closure'],
                   'reflection_sha256': c.digest(c.canonical(reflection).encode())}
        if candidate:
            receipt.update(origin='working-tree', captured_inputs=source['captured_inputs'])
        write(args.work / 'build-receipt.json', receipt)
        snapshot = (c.assemble(reflection, receipt, load(args.work / 'inventory.json'), read)
                    if candidate else c.extract(c.ROOT, source['revision'], reflection, receipt, load(args.work / 'inventory.json')))
        write(args.work / 'snapshot.json', snapshot)
        print(f'reflected {len(snapshot["families"])} families; wrote {args.work / "snapshot.json"}')
    elif args.command == 'promote':
        destination = args.destination.resolve()
        parent = (c.ROOT / 'Test/fixtures/baseline').resolve()
        if destination.parent != parent or destination.name == '66ee4657' or destination.exists():
            raise ValueError('promotion requires a new sibling supplement directory')
        source = load(args.work / 'source.json')
        if source.get('origin', 'git') != 'git' or source['revision'] != c.BASE:
            raise ValueError('only the immutable original revision can be promoted as this supplement')
        for path, expected in [('Extract.lean', source['extractor_sha256']),
                               ('inventory.json', source['inventory_sha256'])]:
            if c.digest((args.work / path).read_bytes()) != expected:
                raise ValueError('promotion input changed after preparation: ' + path)
        snapshot = c.extract(c.ROOT, source['revision'], load(args.work / 'reflection.json'),
                             load(args.work / 'build-receipt.json'), load(args.work / 'inventory.json'))
        if snapshot != load(args.work / 'snapshot.json'):
            raise ValueError('snapshot changed after checked extraction')
        destination.mkdir()
        write(destination / 'snapshot.json', snapshot)
        # Retained recipe text is not a Test module or a new audited import.
        shutil.copyfile(args.work / 'Extract.lean', destination / 'Extract.lean.txt')
        write(destination / 'extraction.json', source)
        print('promoted new supplement; review this new directory: ' + str(destination))
    elif args.command == 'compare-observations':
        report = c.policy_delta(load(args.before), load(args.after), load(args.expected), args.dimension)
        report['inputs'] = {name: c.digest(getattr(args, name).read_bytes()) for name in ('before', 'after', 'expected')}
        if args.out:
            if args.out.resolve().is_relative_to((c.ROOT / 'Test/fixtures/baseline').resolve()):
                raise ValueError('observation comparison cannot write baseline fixtures')
            write(args.out, report)
        print(c.canonical(report), end='')
        return int(report['status'] != 'pass')
    else:
        report = {
            'structural_wire': c.compare(load(args.baseline), load(args.candidate), load(args.policy) if args.policy else None),
            'decoding': {'status': 'not_run', 'reason': 'shape comparison does not execute a decoder'},
            'admission': {'status': 'not_run', 'reason': 'shape comparison does not execute a checker'},
            'execution_permission': {'status': 'not_run', 'reason': 'shape equality grants no permission'},
        }
        if args.out:
            if args.out.resolve().is_relative_to((c.ROOT / 'Test/fixtures/baseline').resolve()):
                raise ValueError('comparison cannot write baseline fixtures')
            write(args.out, report)
        print(c.canonical(report), end='')
        return int(report['structural_wire']['status'] != 'pass')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print('FAIL compatibility: ' + str(error), file=sys.stderr)
        sys.exit(1)
