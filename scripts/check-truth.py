#!/usr/bin/env python3
"""Bounded Lean/rc.112 differential, with pinned host selection and drift refusal.

Two phases, as before: Lean writes the manifest (reading the committed tapes under
harness/truth/tapes, the answers rc.112 gave the package rows last time), bun runs the
generated modules with the recording prelude and writes the observed result and fresh tapes,
and every committed artefact must equal the fresh one. A tape that moved fails the gate the
way corpus.json does: the answers Lean replayed are byte for byte the answers rc.112 just gave.

Between the two, one more refusal (DI-49): the freshly printed modules, their adapter, and the recorder/session sources
must type-check under the one compiler (tsgo, decisions row 57),
`tsgo --noEmit -p harness/truth/tsconfig.json` copied beside them in the work directory.
Running is not being well typed — `pKv.ts` ran for
months while its declared error type disagreed with what the shim could raise (TS2375) — so
the check is on the modules rc.112 just ran, before any byte is compared. Evidence word:
tested; a finite checker run, not byte reproduction (DI-32).

Whether to run at all is the Makefile's decision (`make check-truth` is keyed on the
harness, the tapes, the pinned host manifest and the compiled core); this script always runs.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root / 'scripts/lib'))
import truth_host  # noqa: E402

truth = root / 'harness/truth'


def widening_controls(work, manifest, bun, host_path):
    """One existing Node compiler client batches inferred positives and AST-located mutants."""
    request, response = work/'widening-request.json', work/'widening-receipt.json'
    request.write_text(json.dumps({
        'kind': 'truth-widenings', 'repo': host_path(root), 'work': host_path(work),
        'manifest': json.loads(manifest.read_text())
    }, indent=2) + '\n')
    checked = subprocess.run([
        os.environ.get('EFFECT4_NODE', 'node'), host_path(root/'tools/target/checker.ts'),
        host_path(request), host_path(response)
    ], cwd=root, text=True, capture_output=True, timeout=300)
    if checked.returncode != 0:
        sys.exit('FAIL truth widening: batched tsgo API controls refuse:\n'
                 f'{checked.stdout}{checked.stderr}')
    receipt = json.loads(response.read_text())
    if receipt.get('format') != 'effect4-truth-widenings-v1' or receipt.get('conforms') is not True:
        sys.exit('FAIL truth widening: the structured compiler receipt does not conform')
    # Independent intended values: both union members are real positive observations.
    expected = {
        'pJoinedFirstNumber': {'success': {'some': 1}},
        'pJoinedFirstString': {'success': {'some': 'negative'}},
        'pJoinedModifyNumber': {'success': 1},
        'pJoinedModifyString': {'success': 'negative'},
    }
    rows = json.loads((work/'result.json').read_text())['rows']
    for name, wanted in expected.items():
        matches = [row for row in rows if row['program'] == name]
        if len(matches) != 1 or (matches[0].get('host') or {}).get('exit') != wanted or (matches[0].get('hostSync') or {}).get('exit') != wanted:
            sys.exit(f'FAIL truth widening: {name} must observe intended reply {wanted} on both entries')
    corrupted = receipt.get('corruptedUpdates', [])
    if len(corrupted) != 1 or corrupted[0].get('fixture') != 'pJoinedModifyNumber' or corrupted[0].get('mutationCount') != 2:
        sys.exit('FAIL truth widening: exact corrupted next-state control is missing')
    controls = work/'__widening_queries__'
    controls.mkdir(exist_ok=True)
    mutant = controls/'pJoinedModifyNumber.wrong-update.ts'
    mutant.write_text(corrupted[0]['source'])
    observation_path = controls/'wrong-update.observation.json'
    observed = subprocess.run([
        bun, 'run', host_path(truth/'run-truth.ts'), '--observe', host_path(mutant),
        '--result', host_path(observation_path), '--timeout', '300'
    ], cwd=root, text=True, capture_output=True, timeout=30)
    if observed.returncode != 0:
        sys.exit('FAIL truth widening: corrupted update did not run on the pinned host:\n'
                 f'{observed.stdout}{observed.stderr}')
    observation = json.loads(observation_path.read_text())
    host = observation.get('observation', {})
    sentinel = {'success': 'joinedModify: wrong cell value'}
    if observation.get('status') != 'observed' or observation.get('effect') != '4.0.0-rc.112' or host.get('parked') is not False or host.get('exit') != sentinel:
        sys.exit(f'FAIL truth widening: corrupted update must produce its distinct sentinel: {observation}')
    receipt['intendedPositiveReplies'] = expected
    receipt['corruptedUpdateObservation'] = observation
    response.write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS truth widening: four inferred typed fixtures; two missing-member refusals; corrupted update observed')


def p2b_controls(work, host_path):
    """Check actual typed syntax at source environments; this collection is type-only."""
    manifest_path = work/'p2b-manifest.json'
    subprocess.run(['lake', 'env', 'lean', '-M4096', '--run', 'harness/truth/P2b.lean',
                    str(manifest_path)], cwd=root, check=True, timeout=300)
    manifest = json.loads(manifest_path.read_text())
    directory = work/'__p2b__'
    directory.mkdir()
    # The existing import owner supplies the same header as other printed consumers.
    header = subprocess.run([
        os.environ.get('EFFECT4_NODE', 'node'), '--input-type=module', '-e',
        'import { moduleImports } from "./harness/truth/module-imports.ts"; '
        'console.log(moduleImports("../prelude.ts").join("\\n"))'
    ], cwd=root, text=True, capture_output=True, check=True, timeout=30).stdout.rstrip('\n')
    module = directory/'printed.ts'
    module.write_text(header + '\n\n' + '\n\n'.join(
        fixture['declaration'] for fixture in manifest['fixtures'] + manifest['negativeObservations']) + '\n')
    request, response = work/'p2b-request.json', work/'p2b-receipt.json'
    request.write_text(json.dumps({
        'kind': 'p2b-target', 'repo': host_path(root), 'work': host_path(work),
        'module': host_path(module), 'manifest': manifest
    }, indent=2) + '\n')
    checked = subprocess.run([
        os.environ.get('EFFECT4_NODE', 'node'), host_path(root/'tools/target/checker.ts'),
        host_path(request), host_path(response)
    ], cwd=root, text=True, capture_output=True, timeout=300)
    if checked.returncode != 0:
        sys.exit('FAIL P2b: batched compiler consumer refuses:\n'
                 f'{checked.stdout}{checked.stderr}')
    receipt = json.loads(response.read_text())
    if receipt.get('format') != 'effect4-p2b-target-report-v1':
        sys.exit('FAIL P2b: wrong structured receipt format')
    # Preserve diagnostics and exact columns even when the finite gate refuses.
    checks = ['moduleCompiles', 'exactColumnsAgree', 'expectedNegativesConform', 'mutantsConform', 'conforms']
    failed = [name for name in checks if receipt.get(name) is not True]
    if failed:
        print(json.dumps(receipt, indent=2))
        sys.exit('FAIL P2b: ' + ', '.join(failed))
    print('PASS P2b: exact consumer columns, retained negative comparisons, and missing-member refusals checked; type-only')


def main():
    bun, modules, host_path = truth_host.select(root, truth)

    tapes = truth / 'tapes'
    tapes.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='truth-check-', dir=truth) as work:
        # Generated modules import ../prelude.ts and resolve Effect from their parent tree.
        # Keep the temporary run beneath the selected installation link, as the real run is.
        truth_host.copy_prelude(truth, Path(work))
        # The narrowing controls of `caseTag` and `optionCase` import ./prelude.ts and are named
        # by the tsconfig's `include`; without the copy that pattern matched nothing and no
        # lane compiled them.
        shutil.copyfile(truth/'select-controls.ts', Path(work)/'select-controls.ts')
        shutil.copyfile(truth/'records.typecheck.ts', Path(work)/'records.typecheck.ts')
        # The tuple controls (`tupleAt`, decisions row 159). The config named this file and no
        # copy stood here, so the pinned lane never compiled it (coordinator's addendum 3 to
        # seat T5, 2026-10-05).
        shutil.copyfile(truth/'tuples.typecheck.ts', Path(work)/'tuples.typecheck.ts')
        # The list fold's controls (decisions rows 228 and 229), compiled beside the modules.
        shutil.copyfile(truth/'folds.typecheck.ts', Path(work)/'folds.typecheck.ts')
        # The printed function of an operation's binder term, and a list of number literals
        # (the state plan's T5, decisions row 251), compiled beside the modules.
        shutil.copyfile(truth/'term-rows.typecheck.ts', Path(work)/'term-rows.typecheck.ts')
        # The literal rule of `pair` and `tuple` on the target (decisions row 256): its positive
        # controls and its refusals, compiled beside the modules.
        shutil.copyfile(truth/'literals.typecheck.ts', Path(work)/'literals.typecheck.ts')
        # The Queue's six printed steps, each at the cell's printed type (decisions row 255).
        shutil.copyfile(truth/'queue-steps.typecheck.ts', Path(work)/'queue-steps.typecheck.ts')
        # The mask's saved state at the prelude's alias, in annotated positions (decisions rows
        # 244 to 246): three printed modules and three refusals, compiled beside the modules.
        shutil.copyfile(truth/'mask.typecheck.ts', Path(work)/'mask.typecheck.ts')
        shutil.copytree(truth/'session', Path(work)/'session', ignore=shutil.ignore_patterns('.work'))
        manifest = Path(work)/'corpus.json'
        subprocess.run(['lake', 'env', 'lean', '-M4096', '--run', 'harness/truth/Truth.lean', str(manifest),
                        '--tapes', str(tapes)], cwd=root, check=True, timeout=540)
        subprocess.run([bun, 'run', host_path(truth/'run-truth.ts'), '--manifest', host_path(manifest),
                        '--out', host_path(Path(work)), '--timeout', '300',
                        '--tape-out', host_path(Path(work)/'tapes')], cwd=root, check=True, timeout=180)
        signed = [row for row in json.loads((Path(work)/'result.json').read_text())['rows']
                  if row.get('exception') == 'U-01']
        if len(signed) != 1 or signed[0]['program'] != 'pInterruptEscape':
            sys.exit('FAIL truth: the exact signed U-01 fixture must run once')
        # DI-49: the modules rc.112 just ran, and the adapter they call, under the pinned
        # compiler. The config is copied beside them so that `generated/` and `prelude.ts`
        # resolve as they do in the tree, and `effect`/`@types/bun` through the link above.
        # Check the actual recorder and session sources as well. Copying them flat would
        # break their relative imports of the generated profile; absolute files preserve
        # source topology while prelude/generated are the freshly exercised copies.
        config = json.loads((truth/'tsconfig.json').read_text())
        config['files'] = [host_path(truth/'run-truth.ts')] + [
            host_path(path) for path in sorted((truth/'session').glob('*.ts'))]
        (Path(work)/'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
        # A plain file name in `include` must name a file the compiler reads: one beside the
        # copied config, or one that `files` names in the tree. A name that matches nothing
        # drops its control from the lane without a word. The release driver refuses the same
        # (`type_roots`, scripts/check-truth-release.py).
        by_path = {path.replace('\\', '/').rsplit('/', 1)[-1] for path in config['files']}
        absent = [name for name in config['include']
                  if not any(mark in name for mark in '*?/')
                  and not (Path(work)/name).exists() and name not in by_path]
        if absent:
            sys.exit('FAIL truth: harness/truth/tsconfig.json includes ' + ', '.join(absent)
                     + ', which the work directory does not hold; copy it beside the others')
        typed = subprocess.run(truth_host.compiler(modules) + ['--pretty', 'false',
                                '--noEmit', '-p', host_path(Path(work)/'tsconfig.json')],
                               cwd=work, text=True, capture_output=True, timeout=300)
        if typed.returncode != 0:
            sys.exit('FAIL truth: the regenerated modules do not type-check under '
                     f'harness/truth/tsconfig.json:\n{typed.stdout}{typed.stderr}')
        widening_controls(Path(work), manifest, bun, host_path)
        p2b_controls(Path(work), host_path)
        for name in ['corpus.json', 'result.json', 'result.md']:
            if (Path(work)/name).read_bytes() != (truth/name).read_bytes():
                sys.exit(f'FAIL truth: harness/truth/{name} drifted; inspect the regenerated differential before refreshing (make gen-truth)')
        generated = Path(work)/'generated'
        expected = truth/'generated'
        if sorted(p.name for p in generated.glob('*.ts')) != sorted(p.name for p in expected.glob('*.ts')):
            sys.exit('FAIL truth: generated module inventory drifted')
        for file in generated.glob('*.ts'):
            if file.read_bytes() != (expected/file.name).read_bytes():
                sys.exit(f'FAIL truth: generated module {file.name} drifted')
        fresh = Path(work)/'tapes'
        fresh_names = sorted(p.name for p in fresh.glob('*')) if fresh.is_dir() else []
        if fresh_names != sorted(p.name for p in tapes.glob('*')):
            sys.exit(f'FAIL truth: tape inventory drifted: rc.112 recorded {fresh_names}, committed {sorted(p.name for p in tapes.glob("*"))}; install the fresh tapes deliberately')
        for file in fresh.glob('*') if fresh.is_dir() else []:
            if file.read_bytes() != (tapes/file.name).read_bytes():
                sys.exit(f'FAIL truth: tape {file.name} drifted; rc.112 answered differently from the committed tape')
    print('PASS truth: pinned corpus, bounded differential and signed U-01 divergence checked; '
          'the regenerated modules type-check')
    return 0


if __name__ == '__main__':
    sys.exit(main())
