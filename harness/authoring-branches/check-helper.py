#!/usr/bin/env python3
"""Retain strict ifCase typing, runtime controls, and three independently rejected helpers."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from ts_packet import COMPILER, EFFECT, ROOT, digest, prepare_output, retain_inputs

FILES = ['control.ts', 'prelude-atoms.gen.ts', 'select-controls.ts', 'if-case.test.ts']

PATTERNS = {
    'eager-condition': 'condition, selected construction and selected effect wait for execution',
    'eager-both': 'an unselected poisoned constructor never runs',
    'swapped-selection': 'condition, selected construction and selected effect wait for execution',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    install, output = prepare_output(args.install, args.out)
    records = []

    def recorded(command, work, label, expected_success=True):
        result = subprocess.run(command, cwd=work, text=True, capture_output=True, timeout=300)
        record = {'label': label, 'argv': command, 'cwd': str(work), 'exitCode': result.returncode,
                  'stdout': result.stdout, 'stderr': result.stderr}
        records.append(record)
        (output / (label + '.json')).write_text(json.dumps(record, indent=2) + '\n')
        if expected_success and result.returncode != 0:
            raise RuntimeError(f'{label}: failed with exit {result.returncode}; see retained command output')
        if not expected_success and result.returncode == 0:
            raise RuntimeError(f'{label}: wrong helper passed its intended behavior control')
        return result

    with tempfile.TemporaryDirectory(prefix='effect4-if-case-') as temporary:
        work = Path(temporary)
        original = None
        try:
            (work / 'node_modules').symlink_to(install, target_is_directory=True)
            for name in FILES:
                target = work / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / 'harness/truth' / name, target)
            config = {'compilerOptions': {
                'target': 'ES2022', 'module': 'ESNext', 'moduleResolution': 'bundler',
                'strict': True, 'exactOptionalPropertyTypes': True, 'noUncheckedIndexedAccess': True,
                'verbatimModuleSyntax': True, 'allowImportingTsExtensions': True,
                'noEmit': True, 'skipLibCheck': True, 'types': ['bun'],
            }, 'files': ['select-controls.ts', 'if-case.test.ts'], 'include': []}
            (work / 'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
            compiler = ['node', str(install / '@typescript/native-preview/bin/tsgo')]
            version = recorded(compiler + ['--version'], work, 'compiler-version').stdout.strip()
            if version != 'Version ' + COMPILER:
                raise RuntimeError('Compiler binary differs from the pinned package version')
            runtime = recorded(['bun', '--version'], work, 'runtime-version').stdout.strip()
            node = recorded(['node', '--version'], work, 'node-version').stdout.strip()
            command = compiler + ['--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json')]
            discovery = recorded(command + ['--listFilesOnly'], work, 'compiler-discovery').stdout.splitlines()
            if any(str(work / name) not in discovery for name in config['files']):
                raise RuntimeError('Compiler discovery omitted an assigned observer control')
            recorded(command, work, 'compiler-positive')
            test = ['bun', '--no-install', 'test', str(work / 'if-case.test.ts')]
            recorded(test, work, 'runtime-positive-before')
            original = (work / 'control.ts').read_text()
            start = original.index('export const ifCase = ')
            end = original.index('/** `Eff.select s .option', start)
            signature_end = original.index('=>\n', original.index('): Effect.Effect<A0 | A1, E0 | E1, R0 | R1>', start)) + 3
            signature = original[start:signature_end]
            union = 'Effect.Effect<A0 | A1, E0 | E1, R0 | R1>'
            mutants = {
                'eager-condition': signature +
                    '  (() => { const selected = condition(); return Effect.suspend((): ' + union +
                    ' => selected ? onTrue() : onFalse()) })()\n\n',
                'eager-both': signature +
                    '  Effect.suspend((): ' + union +
                    ' => { const yes = onTrue(); const no = onFalse(); return condition() ? yes : no })\n\n',
                'swapped-selection': signature +
                    '  Effect.suspend((): ' + union + ' => condition() ? onFalse() : onTrue())\n\n',
            }
            for name, helper in mutants.items():
                mutated = original[:start] + helper + original[end:]
                (work / 'control.ts').write_text(mutated)
                mutant_path = output / 'mutants' / name / 'control.ts'
                mutant_path.parent.mkdir(parents=True, exist_ok=True)
                mutant_path.write_text(mutated)
                recorded(command, work, 'compiler-mutant-' + name)
                result = recorded(test + ['--test-name-pattern', PATTERNS[name]], work,
                                  'runtime-mutant-' + name, expected_success=False)
                if PATTERNS[name] not in result.stdout + result.stderr or '(fail)' not in result.stdout + result.stderr:
                    raise RuntimeError(f'{name}: rejection did not identify the intended failing test')
                (work / 'control.ts').write_text(original)
            recorded(test, work, 'runtime-positive-restored')
            recorded(command, work, 'compiler-positive-restored')
            retain_inputs(work, output, FILES + ['tsconfig.json'])
            executables = {name: Path(shutil.which(name)).resolve() for name in ['bun', 'node']}
            receipt = {
                'format': 'effect4-if-case-helper-receipt-v1', 'effect': EFFECT,
                'compiler': COMPILER, 'compilerBinaryVersion': version,
                'runtime': runtime, 'node': node, 'wrongHelpersRejected': list(mutants),
                'commands': records,
                'sourceHashes': {str(p.relative_to(ROOT)): digest(p) for p in
                    [HERE / 'check-helper.py', HERE.parent / 'ts_packet.py'] +
                    [ROOT / 'harness/truth' / name for name in FILES]},
                'compiledHashes': {name: digest(work / name) for name in FILES + ['tsconfig.json']},
                'toolchainHashes': {'effectPackage': digest(install / 'effect/package.json'),
                    'compilerPackage': digest(install / '@typescript/native-preview/package.json'),
                    'compilerEntry': digest(install / '@typescript/native-preview/bin/tsgo'),
                    **{name + 'Executable': digest(path) for name, path in executables.items()}},
                'mutantHashes': {name: digest(output / 'mutants' / name / 'control.ts') for name in mutants},
                'scope': 'Exact inferred A/E/R column checks and independent finite helper runtime controls; no general source-to-target simulation',
            }
            (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        except Exception as error:
            if original is not None:
                (work / 'control.ts').write_text(original)
            retain_inputs(work, output, FILES + ['tsconfig.json'], available_only=True)
            (output / 'failure.txt').write_text(str(error) + '\n')
            raise
    print(f'PASS: strict helper columns and three rejected wrong helpers; Effect {EFFECT}; tsgo {COMPILER}')


if __name__ == '__main__':
    main()
