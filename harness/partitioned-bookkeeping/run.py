#!/usr/bin/env python3
"""Check exact emitted scalar callers; no install, network, or whole-module comparison."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EFFECT = '4.0.1'
COMPILER = '7.0.0-dev.20260629.1'
IDS = ['initialZero', 'initialFive', 'zeroOnZero', 'positiveOnZero', 'zeroAfterTake',
       'takeCapacity', 'insufficient', 'excessive', 'secondTake', 'reservePartial',
       'reserveEmpty', 'reserveCapacity', 'twoReservations', 'forgotDeduction']


def run(command, cwd=ROOT, timeout=300):
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout,
                            env={**os.environ, 'LEAN_NUM_THREADS': '3'})
    if result.returncode:
        raise RuntimeError(f'{command}: exit {result.returncode}\n{result.stdout}{result.stderr}')
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    install, output = args.install.resolve(), args.out.resolve()
    for name, expected in [('effect', EFFECT), ('@typescript/native-preview', COMPILER)]:
        if json.loads((install / name / 'package.json').read_text())['version'] != expected:
            raise RuntimeError(f'Wrong installed {name} version')
    if output.exists() and any(output.iterdir()):
        raise RuntimeError('Refuse to overwrite retained evidence')
    output.mkdir(parents=True, exist_ok=True)
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
    with tempfile.TemporaryDirectory(prefix='partitioned-bookkeeping-') as temp:
        work = Path(temp)
        (work / 'node_modules').symlink_to(install, target_is_directory=True)
        prelude_files = ['prelude-atoms.gen.ts', 'records.ts', 'tuples.ts']
        for name in prelude_files:
            shutil.copyfile(ROOT / 'harness/truth' / name, work / name)
        (work / 'prelude.ts').write_text(''.join(f'export * from "./{name}"\n' for name in prelude_files))
        helpers = run(['bun', '--no-install', '-e', 'import * as H from "./prelude.ts"; console.log(Object.keys(H).join(", "))'], cwd=work).strip()
        header = 'import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "effect"\n'
        header += f'import {{ {helpers} }} from "./prelude.ts"\n'
        for c in cases:
            (work / c['file']).write_text(header + (output / c['file']).read_text())
        shutil.copyfile(HERE / 'observe.ts', work / 'observe.ts')
        shutil.copyfile(output / 'manifest.json', work / 'manifest.json')
        config = {'compilerOptions': {'target': 'ES2022', 'module': 'ESNext', 'moduleResolution': 'bundler',
                  'strict': True, 'exactOptionalPropertyTypes': True, 'noUncheckedIndexedAccess': True,
                  'verbatimModuleSyntax': True, 'allowImportingTsExtensions': True, 'noEmit': True,
                  'skipLibCheck': True, 'types': ['bun']},
                  'files': [c['file'] for c in cases] + ['observe.ts'], 'include': []}
        (work / 'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
        compiler = ['node', str(install / '@typescript/native-preview/bin/tsgo')]
        if run(compiler + ['--version'], cwd=work).strip() != 'Version ' + COMPILER:
            raise RuntimeError('Wrong compiler binary version')
        command = compiler + ['--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json')]
        discovered = run(command + ['--listFilesOnly'], cwd=work).splitlines()
        if any(str(work / name) not in discovered for name in config['files']):
            raise RuntimeError('Compiler discovery omitted a caller')
        diagnostics = run(command, cwd=work)
        rows = json.loads(run(['bun', '--no-install', str(work / 'observe.ts'), str(work)], cwd=work))
        if [row['id'] for row in rows] != IDS:
            raise RuntimeError('Runtime discovery differs from the case inventory')
        for row, c in zip(rows, cases):
            if row['observed'] != c['expected']:
                raise RuntimeError(f'{c["id"]}: emitted result differs from the checked expected observation')
        correct, wrong = rows[5]['observed'], rows[-1]['observed']
        if correct != [True, [5, 0, 0]] or wrong != [True, [5, 5, 0]] or correct == wrong:
            raise RuntimeError('The wrong-update control did not keep its reply and change its stored count')
        retained = config['files'] + prelude_files + ['prelude.ts', 'tsconfig.json', 'manifest.json']
        for name in retained:
            target = output / 'compiled-inputs' / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(work / name, target)
        sources = [HERE / 'Produce.lean', HERE / 'observe.ts', HERE / 'run.py',
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
