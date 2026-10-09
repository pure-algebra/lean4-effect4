#!/usr/bin/env python3
"""Check finite public module callers and selected latest observations; no whole-module theorem."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from ts_packet import COMPILER, EFFECT, ROOT, compiled_packet, digest, prepare_output, retain_inputs, run

IDS = ['streamInline', 'streamEmpty', 'streamDefinitions', 'streamRepeated', 'streamIndependent',
       'streamCapture', 'syncNumeric', 'syncCollision', 'syncDepth', 'syncFold', 'syncStrings', 'wrongSticky']


READ_BACK = {name: ('frozen-ref-definition-refusal' if name in
                   {'streamDefinitions', 'streamRepeated', 'streamIndependent'} else 'exact')
             for name in IDS}


def read_back_inventory(cases):
    statuses = {c['id']: c.get('readBack') for c in cases}
    if statuses != READ_BACK:
        raise RuntimeError('Read-back results differ from the exact per-case status inventory')
    return statuses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    install, output = prepare_output(args.install, args.out)
    if not args.skip_build:
        print(run(['lake', 'build', 'Test.Program.StreamArray', 'Test.Program.SynchronizedRef'], timeout=900), end='')
    print(run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', str(HERE / 'Produce.lean'), str(output)]), end='')
    manifest = json.loads((output / 'manifest.json').read_text())
    cases = manifest['cases']
    if manifest.get('format') != 'effect4-module-catalogue-v1' or [c['id'] for c in cases] != IDS:
        raise RuntimeError('Missing, duplicated, extra, or reordered caller')
    read_back = read_back_inventory(cases)
    if sorted(p.name for p in output.glob('*.ts')) != sorted(c['file'] for c in cases):
        raise RuntimeError('The emitted files differ from the case inventory')
    emitted_hashes = {c['file']: digest(output / c['file']) for c in cases}
    with compiled_packet(install, output, [c['file'] for c in cases], HERE / 'observe.ts',
                         'module-catalogue-') as (work, diagnostics, retained):
        observed = json.loads(run(['bun', '--no-install', str(work / 'observe.ts'), str(work)], cwd=work))
        rows = observed['rows']
        if [row['id'] for row in rows] != IDS:
            raise RuntimeError('Runtime discovery differs from the case inventory')
        for row, c in zip(rows, cases):
            if row['observed'] != c['expected']:
                raise RuntimeError(f'{c["id"]}: emitted result differs from the checked expected observation')
        latest = observed['latest']
        if latest != {'stream': [1, 2, 3], 'empty': [], 'sync': [5, 7], 'strings': ['before', 'after']}:
            raise RuntimeError('Latest module observations differ')
        if rows[0]['observed'] != latest['stream'] or rows[1]['observed'] != latest['empty']:
            raise RuntimeError('Stream collection differs from latest in the finite comparison')
        if rows[6]['observed'][:2] != latest['sync'] or rows[10]['observed'][:2] != latest['strings']:
            raise RuntimeError('SynchronizedRef reply/final value differs from latest in the finite comparison')
        if rows[-1]['observed'] != [[1, 2, 3], [1, 2, 3]] or rows[-1]['observed'] == [[1, 2, 3], []]:
            raise RuntimeError('The deliberately sticky array did not expose repeated data')
        retain_inputs(work, output, retained)
        sources = [HERE.parent / 'ts_packet.py', HERE / 'Produce.lean', HERE / 'observe.ts', HERE / 'run.py',
                   ROOT / 'Test/Program/StreamArray.lean', ROOT / 'Test/Program/SynchronizedRef.lean']
        sources += sorted((ROOT / 'src/Effect4/Library/Stream').glob('Array*.lean'))
        sources += sorted((ROOT / 'src/Effect4/Library/SynchronizedRef').glob('*.lean'))
        sources += [ROOT / 'vendor/effect-4.0.1/src' / f'{m}.ts' for m in ['Stream', 'Channel', 'SynchronizedRef', 'Ref', 'Semaphore']]
        receipt = {'format': 'effect4-module-catalogue-receipt-v1', 'effect': EFFECT, 'compiler': COMPILER,
                   'runtime': run(['bun', '--version'], cwd=work).strip(), 'positive': len(cases) - 1,
                   'wrongStickyDetected': True, 'rows': rows, 'readBack': read_back, 'latest': latest, 'compilerDiagnostics': diagnostics,
                   'sourceHashes': {str(p.relative_to(ROOT)): digest(p) for p in sources},
                   'emittedHashes': emitted_hashes, 'compiledHashes': {name: digest(work / name) for name in retained},
                   'scope': 'Finite emitted public module callers, plus latest Stream collection and SynchronizedRef reply/final value; no scheduler or whole-module agreement'}
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if any(digest(output / name) != expected for name, expected in emitted_hashes.items()):
        raise RuntimeError('An emitted file changed during validation')
    print(f'PASS: {len(cases)-1} module callers and wrong-sticky control; 9 exact read-backs and 3 frozen refusals; Effect {EFFECT}; tsgo {COMPILER}')


if __name__ == '__main__':
    main()
