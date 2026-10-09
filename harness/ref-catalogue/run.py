#!/usr/bin/env python3
"""Finite Ref machine/emitted-TypeScript/latest-host packet; no network or full sweep."""
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
OPERATIONS = ['make', 'get', 'set', 'getAndSet', 'setAndGet', 'update', 'getAndUpdate',
              'updateAndGet', 'updateSome', 'getAndUpdateSome', 'updateSomeAndGet', 'modify', 'modifySome']
IDS = OPERATIONS + [name + 'None' for name in ['updateSome', 'getAndUpdateSome', 'updateSomeAndGet', 'modifySome']] + ['captureAcc', 'captureItem', 'string', 'allocatedHandle']


def run(command, cwd=ROOT, timeout=300):
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout,
                            env={**os.environ, 'LEAN_NUM_THREADS': '3'})
    if result.returncode:
        raise RuntimeError(f'{command}: exit {result.returncode}\n{result.stdout}{result.stderr}')
    return result.stdout


def version(install, name):
    return json.loads((install / name / 'package.json').read_text())['version']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', type=Path, required=True, help='Explicit latest Effect and pinned compiler node_modules')
    parser.add_argument('--out', type=Path, required=True, help='Retained packet directory')
    parser.add_argument('--skip-build', action='store_true', help='The narrow consumer build already passed')
    args = parser.parse_args()
    install, output = args.install.resolve(), args.out.resolve()
    if version(install, 'effect') != EFFECT or version(install, '@typescript/native-preview') != COMPILER:
        raise RuntimeError('The selected Effect or compiler version differs from the packet pins')
    if output.exists() and any(output.iterdir()):
        raise RuntimeError('Output directory must be empty; retained evidence is never overwritten')
    output.mkdir(parents=True, exist_ok=True)
    if not args.skip_build:
        print(run(['lake', 'build', 'Test.Program.RefFaces'], timeout=900), end='')
    print(run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
               str(HERE / 'Produce.lean'), str(output)]), end='')
    manifest = json.loads((output / 'manifest.json').read_text())
    cases = manifest['cases']
    if manifest.get('format') != 'effect4-ref-catalogue-v1' or manifest['operations'] != OPERATIONS:
        raise RuntimeError('Wrong packet format or operation inventory')
    if [c['id'] for c in cases] != IDS or len(set(IDS)) != 21:
        raise RuntimeError('Missing, duplicate, reordered, or extra caller')
    if sorted(p.name for p in output.glob('*.ts')) != sorted(c['file'] for c in cases):
        raise RuntimeError('Emitted file inventory differs from the manifest')
    if any(c['machine'] != c['expected'] for c in cases):
        raise RuntimeError('A machine observation differs from the independent expected value')
    for c in cases:
        if f'Ref.{c["operation"]}(' not in (output / c['file']).read_text():
            raise RuntimeError(f'{c["id"]}: emitted caller does not use its declared public operation')
    input_hashes = {c['file']: digest(output / c['file']) for c in cases}
    with tempfile.TemporaryDirectory(prefix='ref-catalogue-') as temp:
        work = Path(temp)
        (work / 'node_modules').symlink_to(install, target_is_directory=True)
        for name in ['prelude-atoms.gen.ts', 'records.ts', 'tuples.ts']:
            shutil.copyfile(ROOT / 'harness/truth' / name, work / name)
        (work / 'prelude.ts').write_text('export * from "./prelude-atoms.gen.ts"\nexport * from "./records.ts"\nexport * from "./tuples.ts"\n')
        header = 'import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "effect"\nimport * as Helpers from "./prelude.ts"\n'
        # Every printed helper comes from the existing prelude; import its actual export list.
        helpers = run(['bun', '--no-install', '-e', f'import * as H from {json.dumps(str(work / "prelude.ts"))}; console.log(Object.keys(H).join(", "))'], cwd=work).strip()
        header = header.split('import * as Helpers')[0] + f'import {{ {helpers} }} from "./prelude.ts"\n'
        for c in cases:
            (work / c['file']).write_text(header + (output / c['file']).read_text())
        original = (work / 'modify.ts').read_text()
        import re
        mutant, count = re.subn(r'pair\(41, add\((a\d+), (a\d+)\)\)', r'pair(41, \1)', original)
        if count != 1:
            raise RuntimeError(f'Wrong-update control found {count} update sites, expected one')
        (work / 'wrong-update.ts').write_text(mutant)
        for name in ['controls.ts', 'observe.ts']:
            shutil.copyfile(HERE / name, work / name)
        shutil.copyfile(output / 'manifest.json', work / 'manifest.json')
        config = {'compilerOptions': {'target': 'ES2022', 'module': 'ESNext', 'moduleResolution': 'bundler',
                  'strict': True, 'exactOptionalPropertyTypes': True, 'noUncheckedIndexedAccess': True,
                  'verbatimModuleSyntax': True, 'allowImportingTsExtensions': True, 'noEmit': True,
                  'skipLibCheck': True, 'types': ['bun']},
                  'files': [c['file'] for c in cases] + ['wrong-update.ts', 'controls.ts', 'observe.ts'], 'include': []}
        (work / 'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
        compiler = ['node', str(install / '@typescript/native-preview/bin/tsgo')]
        found_version = run(compiler + ['--version'], cwd=work).strip()
        if found_version != 'Version ' + COMPILER:
            raise RuntimeError(f'Wrong detected compiler: {found_version}')
        command = compiler + ['--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json')]
        files = run(command + ['--listFilesOnly'], cwd=work).splitlines()
        if any(str(work / name) not in files for name in config['files']):
            raise RuntimeError('Compiler discovery omitted a caller or control')
        diagnostics = run(command, cwd=work)
        # Remove the four expected-error directives in an isolated file. Each fault must
        # produce a diagnostic at its own source line, then the restored project must pass.
        control_text = (work / 'controls.ts').read_text()
        control_lines = control_text.splitlines()
        expected_lines = [i + 2 for i, line in enumerate(control_lines) if '@ts-expect-error' in line]
        if len(expected_lines) != 4:
            raise RuntimeError('The compiler control inventory differs from four intended faults')
        red_text = '\n'.join('' if '@ts-expect-error' in line else line for line in control_lines) + '\n'
        (work / 'controls.red.ts').write_text(red_text)
        red_config = {**config, 'files': [name if name != 'controls.ts' else 'controls.red.ts' for name in config['files']]}
        (work / 'tsconfig.red.json').write_text(json.dumps(red_config) + '\n')
        red = subprocess.run(compiler + ['--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.red.json')],
                             cwd=work, capture_output=True, text=True, timeout=300)
        red_diagnostics = red.stdout + red.stderr
        diagnostic_lines = [int(n) for n in re.findall(r'controls\.red\.ts\((\d+),\d+\): error TS\d+', red_diagnostics)]
        if red.returncode == 0 or sorted(diagnostic_lines) != expected_lines:
            raise RuntimeError(f'The intended compiler refusals differ: {red_diagnostics}')
        run(command, cwd=work)
        observed = json.loads(run(['bun', '--no-install', 'run', str(work / 'observe.ts'), str(work)], cwd=work))
        if [row['id'] for row in observed['rows']] != IDS:
            raise RuntimeError('Host discovery omitted or reordered a caller')
        for row, c in zip(observed['rows'], cases):
            if row['observed'] != c['expected']:
                raise RuntimeError(f'{row["id"]}: host {row["observed"]} differs from {c["expected"]}')
        if observed['mutant'] != [41, 5] or observed['mutant'] == manifest['cases'][11]['expected']:
            raise RuntimeError('The wrong-update control did not retain its reply and change its cell')
        if observed['rawSet'] != {'backing': True, 'outer': False, 'next': 7}:
            raise RuntimeError('The raw set runtime boundary differs from the retained control')
        # The compiler also accepts the mutant; the runtime observation is the intended detector.
        receipt = {'format': 'effect4-ref-catalogue-receipt-v1', 'effect': EFFECT, 'compiler': COMPILER,
                   'runtime': run(['bun', '--version'], cwd=work).strip(), 'caseCount': len(cases),
                    'ids': IDS, 'inputHashes': input_hashes,
                   'sourceHashes': {name: digest(ROOT / name) for name in [
                       'Test/Program/RefPrograms.lean', 'Test/Program/RefFaces.lean',
                       'src/Effect4/Step/Callback.lean', 'harness/ref-catalogue/Produce.lean',
                       'harness/ref-catalogue/controls.ts', 'harness/ref-catalogue/observe.ts',
                       'harness/ref-catalogue/run.py']},
                   'preludeHashes': {name: digest(work / name) for name in ['prelude-atoms.gen.ts', 'records.ts', 'tuples.ts']},
                    'compilerFiles': config['files'], 'compilerDiagnostics': diagnostics,
                   'negativeControlLines': expected_lines,
                   'negativeControlDiagnostics': red_diagnostics.replace(str(work), '<work>'),
                   'compiledInputHashes': {name: digest(work / name) for name in config['files']},
                   'host': observed, 'mutantCount': count, 'conforms': True}
        for name in config['files'] + ['controls.red.ts', 'tsconfig.red.json', 'prelude.ts', 'prelude-atoms.gen.ts', 'records.ts', 'tuples.ts', 'tsconfig.json']:
            target = output / 'compiled-inputs' / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(work / name, target)
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if any(digest(output / name) != wanted for name, wanted in input_hashes.items()):
        raise RuntimeError('An emitted input changed during validation')
    print(f'PASS Ref catalogue: {len(cases)} checked callers on Effect {EFFECT}; tsgo {COMPILER}; stored-state mutant detected')


if __name__ == '__main__':
    main()
