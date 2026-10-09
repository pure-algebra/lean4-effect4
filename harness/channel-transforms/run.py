#!/usr/bin/env python3
"""Check exact emitted numeric Channel modules and discriminate wrong completion transformation."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from ts_packet import COMPILER, EFFECT, ROOT, compiled_packet, digest, prepare_output, retain_inputs, run

EXPECTED = [('batchMap', 30), ('effectMap', 2), ('completionMap', 43),
            ('nestedCompletion', 43), ('collectClose', 103), ('forEachClose', 103),
            ('upstreamState', 7), ('mapperState', 8), ('wrongBatchIdentity', 10),
            ('wrongNoIncrement', 42)]
IDS = [name for name, _ in EXPECTED]
CONTROLS = {'wrongBatchIdentity', 'wrongNoIncrement'}


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
        print(recorded(['lake', 'build', 'Test.Program.Channel'], timeout=900), end='')
    print(recorded(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                    str(HERE / 'Produce.lean'), str(output)]), end='')
    manifest = json.loads((output / 'manifest.json').read_text())
    cases = manifest['cases']
    if manifest.get('format') != 'effect4-channel-transforms-v1' or manifest.get('fuel') != 10000:
        raise RuntimeError('Wrong packet format or Lean observation budget')
    if [c['id'] for c in cases] != IDS:
        raise RuntimeError('Missing, duplicated, extra, or reordered caller')
    for c, (name, expected) in zip(cases, EXPECTED):
        if (c['file'] != name + '.ts' or type(c['expected']) is not int
                or type(c['leanObserved']) is not int or c['expected'] != expected
                or c['leanObserved'] != expected or c['wrongControl'] is not (name in CONTROLS)):
            raise RuntimeError(f'{name}: manifest differs from the fixed numeric case inventory')
        reading = c.get('readBack', {})
        unreadable = reading.get('unreadableHeaders')
        if (reading.get('status') != 'refused' or reading.get('shape') != 'definition'
                or not isinstance(unreadable, list) or not unreadable
                or any(not isinstance(header, str) or not header for header in unreadable)):
            raise RuntimeError(f'{name}: missing the expected unreadable-definition-header evidence')
    if sorted(p.name for p in output.glob('*.ts')) != sorted(c['file'] for c in cases):
        raise RuntimeError('The emitted files differ from the case inventory')
    emitted_hashes = {c['file']: digest(output / c['file']) for c in cases}
    manifest_hash = digest(output / 'manifest.json')
    with compiled_packet(install, output, [c['file'] for c in cases], HERE / 'observe.ts',
                         'channel-transforms-') as (work, diagnostics, retained):
        compiler = ['node', str(install / '@typescript/native-preview/bin/tsgo')]
        # These are the exact successful compiler commands issued by compiled_packet.
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
        observed = {}
        for row, (name, expected) in zip(rows, EXPECTED):
            if type(row['observed']) is not int or row['observed'] != expected:
                raise RuntimeError(f'{name}: emitted result differs from the fixed expected observation')
            observed[name] = row['observed']
        for correct, wrong, expected_correct, expected_wrong in [
                ('completionMap', 'wrongNoIncrement', 43, 42),
                ('batchMap', 'wrongBatchIdentity', 30, 10)]:
            if (observed[correct] != expected_correct or observed[wrong] != expected_wrong
                    or observed[correct] == observed[wrong]):
                raise RuntimeError(f'{wrong}: observation did not distinguish the wrong transformation')
        retain_inputs(work, output, retained)
        sources = [HERE.parent / 'ts_packet.py', HERE / 'Produce.lean', HERE / 'observe.ts', HERE / 'run.py',
                   ROOT / 'Test/Program/Channel.lean', ROOT / 'src/Effect4/Program/Stream.lean',
                   ROOT / 'src/Effect4/Program/Authoring/Module.lean']
        sources += [ROOT / path for path in [
            'src/Effect4/Library/Channel/Ops.lean',
            'src/Effect4/Codegen/Read.lean',
            'src/Effect4/Library/Pull/Ops.lean',
            'src/Effect4/Library/Stream/Source.lean',
            'src/Effect4/Library/Stream/Definitions.lean',
            'src/Effect4/Library/Stream/Ops.lean',
            'src/Effect4/Library/Stream/Steps.lean',
            'src/Effect4/Laws/Library/Stream/Definitions.lean',
            'src/Effect4/Laws/Library/Channel/Scope.lean',
            'src/Effect4/Laws/Library/Channel/Protocol.lean',
            'vendor/effect-4.0.1/src/Channel.ts',
        ]]
        runtime = recorded(['bun', '--version'], cwd=work).strip()
        receipt = {
            'format': 'effect4-channel-transforms-receipt-v1', 'effect': EFFECT, 'compiler': COMPILER,
            'runtime': runtime, 'positive': len(EXPECTED) - len(CONTROLS),
            'wrongTransformControls': len(CONTROLS), 'wrongTransformDetected': True,
            'sourceReading': 'Expected definition-header refusal retained for every module; no read-back claim',
            'rows': rows, 'compilerDiagnostics': diagnostics, 'commands': commands,
            'sourceHashes': {str(p.relative_to(ROOT)): digest(p) for p in sources},
            'toolchainHashes': {'effectPackage': digest(install / 'effect/package.json'),
                               'compilerPackage': digest(install / '@typescript/native-preview/package.json')},
            'manifestHash': manifest_hash, 'emittedHashes': emitted_hashes,
            'compiledHashes': {name: digest(work / name) for name in retained},
            'scope': 'Finite exact emitted numeric stored modules using whole-batch Channel maps and signed End values; no native Channel Done-cause correspondence, asynchronous progress or whole-stream target simulation',
        }
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if digest(output / 'manifest.json') != manifest_hash:
        raise RuntimeError('The manifest changed during validation')
    if any(digest(output / name) != expected for name, expected in emitted_hashes.items()):
        raise RuntimeError('An emitted file changed during validation')
    print(f'PASS: {len(EXPECTED)-len(CONTROLS)} numeric callers and {len(CONTROLS)} wrong-transform controls; '
          f'Effect {EFFECT}; tsgo {COMPILER}')


if __name__ == '__main__':
    main()
