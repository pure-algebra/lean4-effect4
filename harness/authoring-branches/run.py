#!/usr/bin/env python3
"""Check ordinary authored branches through Lean admission, reading, target checking and finite execution."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from ts_packet import COMPILER, EFFECT, ROOT, compiled_packet, digest, prepare_output, retain_inputs, run

# This inventory is independent of the producer's manifest and computed Lean answers.
EXPECTED = [('plainTrue', 7), ('plainFalse', 9), ('batchTrue', 3), ('batchFalse', 42),
            ('errorLeft', 11), ('errorRight', 22), ('stateTrue', 1), ('stateFalse', 10),
            ('stateFailure', 7), ('serviceTrue', 17), ('serviceFalse', 9)]
IDS = [name for name, _ in EXPECTED]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    install, output = prepare_output(args.install, args.out)
    commands = []

    def recorded(command, *, cwd=ROOT, timeout=300):
        commands.append({'argv': command, 'cwd': str(cwd)})
        return run(command, cwd=cwd, timeout=timeout)

    if not args.skip_build:
        print(recorded(['lake', 'build', 'Test.Program.BranchAuthoring'], timeout=900), end='')
    print(recorded(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                    str(HERE / 'Produce.lean'), str(output)]), end='')
    manifest = json.loads((output / 'manifest.json').read_text())
    cases = manifest['cases']
    if manifest.get('format') != 'effect4-authoring-branches-v1' or manifest.get('fuel') != 10000:
        raise RuntimeError('Wrong packet format or observation budget')
    if [c['id'] for c in cases] != IDS:
        raise RuntimeError('Missing, duplicated, extra, or reordered caller')
    for c, (name, expected) in zip(cases, EXPECTED):
        if (c['file'] != name + '.ts' or type(c['expected']) is not int
                or type(c['leanObserved']) is not int or c['expected'] != expected
                or c['leanObserved'] != expected):
            raise RuntimeError(f'{name}: manifest differs from the fixed numeric observations')
        if c.get('readBack') != {'status': 'accepted'}:
            raise RuntimeError(f'{name}: missing successful source reconstruction')
    if sorted(p.name for p in output.glob('*.ts')) != sorted(c['file'] for c in cases):
        raise RuntimeError('The emitted files differ from the case inventory')
    emitted_hashes = {c['file']: digest(output / c['file']) for c in cases}
    manifest_hash = digest(output / 'manifest.json')
    with compiled_packet(install, output, [c['file'] for c in cases], HERE / 'observe.ts',
                         'authoring-branches-') as (work, diagnostics, retained):
        compiler = ['node', str(install / '@typescript/native-preview/bin/tsgo')]
        commands.extend([
            {'argv': compiler + ['--version'], 'cwd': str(work)},
            {'argv': compiler + ['--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json'),
                                 '--listFilesOnly'], 'cwd': str(work)},
            {'argv': compiler + ['--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json')],
             'cwd': str(work)},
        ])
        rows = json.loads(recorded(['bun', '--no-install', str(work / 'observe.ts'), str(work)], cwd=work))
        if [row['id'] for row in rows] != IDS:
            raise RuntimeError('Runtime discovery differs from the case inventory')
        for row, (name, expected) in zip(rows, EXPECTED):
            if type(row['observed']) is not int or row['observed'] != expected:
                raise RuntimeError(f'{name}: generated result differs from the independent observation')
        retain_inputs(work, output, retained)
        sources = [HERE.parent / 'ts_packet.py', HERE / 'Produce.lean', HERE / 'observe.ts', HERE / 'run.py']
        sources += [ROOT / path for path in [
            'Test/Program/BranchAuthoring.lean', 'src/Effect4/Codegen/Templates.lean',
            'src/Effect4/Codegen/PrintLeaf.lean', 'src/Effect4/Codegen/PrintEliminators.lean',
            'src/Effect4/Codegen/EraseTypes.lean', 'src/Effect4/Codegen/Read.lean',
            'harness/truth/control.ts', 'harness/truth/prelude.ts',
        ]]
        receipt = {
            'format': 'effect4-authoring-branches-receipt-v1', 'effect': EFFECT, 'compiler': COMPILER,
            'runtime': recorded(['bun', '--version'], cwd=work).strip(), 'positive': len(EXPECTED),
            'rows': rows, 'sourceReading': 'Every emitted module reads back to its admitted program',
            'compilerDiagnostics': diagnostics, 'commands': commands,
            'sourceHashes': {str(p.relative_to(ROOT)): digest(p) for p in sources},
            'toolchainHashes': {'effectPackage': digest(install / 'effect/package.json'),
                               'compilerPackage': digest(install / '@typescript/native-preview/package.json')},
            'manifestHash': manifest_hash, 'emittedHashes': emitted_hashes,
            'compiledHashes': {name: digest(work / name) for name in retained},
            'scope': 'Finite authored boolean branches with separate success, error and service columns; '
                     'selected writes and failures; syntax read-back; no general host simulation or scheduler claim',
        }
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if digest(output / 'manifest.json') != manifest_hash:
        raise RuntimeError('The manifest changed during validation')
    if any(digest(output / name) != expected for name, expected in emitted_hashes.items()):
        raise RuntimeError('An emitted file changed during validation')
    print(f'PASS: {len(EXPECTED)} authored branches; read-back; Effect {EFFECT}; tsgo {COMPILER}')


if __name__ == '__main__':
    main()
