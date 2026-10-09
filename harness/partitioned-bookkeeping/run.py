#!/usr/bin/env python3
"""Check exact emitted scalar callers; no install, network, or whole-module comparison."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from ts_packet import COMPILER, EFFECT, ROOT, compiled_packet, digest, prepare_output, retain_inputs, run

IDS = ['initialZero', 'initialFive', 'zeroOnZero', 'positiveOnZero', 'zeroAfterTake',
       'takeCapacity', 'insufficient', 'excessive', 'secondTake', 'reservePartial',
       'reserveEmpty', 'reserveCapacity', 'twoReservations', 'forgotDeduction']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    install, output = prepare_output(args.install, args.out)
    if not args.skip_build:
        print(run(['lake', 'build', 'Test.Program.PartitionedSemaphoreFaces'], timeout=900), end='')
    print(run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', str(HERE / 'Produce.lean'), str(output)]), end='')
    manifest = json.loads((output / 'manifest.json').read_text())
    cases = manifest['cases']
    if manifest.get('format') != 'effect4-partitioned-bookkeeping-v1' or [c['id'] for c in cases] != IDS:
        raise RuntimeError('Missing, duplicated, extra, or reordered caller')
    if sorted(p.name for p in output.glob('*.ts')) != sorted(c['file'] for c in cases):
        raise RuntimeError('The emitted files differ from the case inventory')
    emitted_hashes = {c['file']: digest(output / c['file']) for c in cases}
    with compiled_packet(install, output, [c['file'] for c in cases], HERE / 'observe.ts',
                         'partitioned-bookkeeping-') as (work, diagnostics, retained):
        rows = json.loads(run(['bun', '--no-install', str(work / 'observe.ts'), str(work)], cwd=work))
        if [row['id'] for row in rows] != IDS:
            raise RuntimeError('Runtime discovery differs from the case inventory')
        for row, c in zip(rows, cases):
            if row['observed'] != c['expected']:
                raise RuntimeError(f'{c["id"]}: emitted result differs from the checked expected observation')
        correct, wrong = rows[5]['observed'], rows[-1]['observed']
        if correct != [True, [5, 0, 0]] or wrong != [True, [5, 5, 0]] or correct == wrong:
            raise RuntimeError('The wrong-update control did not keep its reply and change its stored count')
        retain_inputs(work, output, retained)
        sources = [HERE.parent / 'ts_packet.py', HERE / 'Produce.lean', HERE / 'observe.ts', HERE / 'run.py',
                   ROOT / 'Test/Program/PartitionedSemaphorePrograms.lean',
                   ROOT / 'Test/Program/PartitionedSemaphoreFaces.lean']
        sources += sorted((ROOT / 'src/Effect4/Library/PartitionedSemaphore').glob('*.lean'))
        receipt = {'format': 'effect4-partitioned-bookkeeping-receipt-v1', 'effect': EFFECT, 'compiler': COMPILER,
                   'runtime': run(['bun', '--version'], cwd=work).strip(), 'positive': len(cases) - 1,
                   'wrongUpdateDetected': True, 'rows': rows, 'compilerDiagnostics': diagnostics,
                   'sourceHashes': {str(p.relative_to(ROOT)): digest(p) for p in sources},
                   'emittedHashes': emitted_hashes, 'compiledHashes': {name: digest(work / name) for name in retained},
                   'scope': 'Finite emitted scalar callers through Effect Ref; no native PartitionedSemaphore wrapper comparison'}
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if any(digest(output / name) != expected for name, expected in emitted_hashes.items()):
        raise RuntimeError('An emitted file changed during validation')
    print(f'PASS: {len(cases)-1} scalar callers and wrong-update control; Effect {EFFECT}; tsgo {COMPILER}')


if __name__ == '__main__':
    main()
