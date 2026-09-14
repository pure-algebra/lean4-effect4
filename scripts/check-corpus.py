#!/usr/bin/env python3
"""The generated corpus against rc.112 and the TypeScript compiler, one row per program.

`make check-corpus`. Four steps, then one expected file:

1. Lean writes the manifest of the generated corpus (`harness/truth/Truth.lean --corpus`,
   the 400 programs of `Test/Program/Gen.lean` at depth 4, each with its type, its printed
   module, the machine's run and whether it is in the fragment `run_eq_meaning` covers).
2. The truth runner (`harness/truth/run-truth.ts`) prints one module per program under
   `harness/truth/corpus-check/generated/`, runs each on the pinned `effect@4.0.0-rc.112`
   and compares rc.112's exit and schedule with the machine's; nothing is patched.
3. `tsc` type-checks every generated module under the harness's compiler options.
4. `tools/target/corpus.ts` compares Lean's answer, error and requirement types with the
   types `tsc` infers for the printed module, both assignment directions, on every
   well-typed program.

The result is `harness/truth/corpus-results.tsv`: name, `straight`, `wellTyped`, `tsc`
(clean/errors), `run` (the run outcome), Lean's exit, rc.112's exit, `types` (the type
outcome) and the runner's note. The committed file is the expected one: the check fails
when a fresh run differs (the diff names the programs) and when a row records a
disagreement that `harness/truth/corpus-known-differences.md` does not list. `--promote`
writes the fresh file and only reports the unregistered rows.

Only well-typed programs with a Lean verdict are run, each in its own process with a kill
timeout: the run comparison is a claim about programs the rules admit, and a printed program
can loop forever on rc.112 inside a synchronous loop that no in-process deadline interrupts.
Run outcomes: `agree` (exit and schedule), `schedule-differs`, `both-park` (neither face
settled within the deadline — reported, never counted as agreement), `host-timeout` (Lean
settles, rc.112 does not, within the deadline), `host-hang` (the process had to be killed),
`untyped` (ill-typed in Lean, not run), `lean-frontier` (the machine ran out of fuel, no
verdict, not run), `refused-by-printer`, `host-load-error`, `differ`. Type outcomes: `agree`,
`mismatch-<axes>`, `refused` (an input the oracle cannot bind, e.g. an undischarged
service key), `untyped` (ill-typed in Lean, not queried; the `tsc` column says whether the
printed module types anyway).
"""
import difflib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root / 'scripts/lib'))
import truth_host  # noqa: E402

truth = root / 'harness/truth'
WORK = truth / 'corpus-check'
EXPECTED = truth / 'corpus-results.tsv'
KNOWN = truth / 'corpus-known-differences.md'
COUNT, DEPTH, TIMEOUT_MS, PROGRAM_TIMEOUT_S = 400, 4, 300, 30
COLUMNS = ['name', 'straight', 'wellTyped', 'tsc', 'run', 'lean', 'host', 'types', 'note']
DISAGREEMENTS = {'differ', 'schedule-differs', 'host-timeout', 'host-hang', 'host-load-error'}


def verdict(entry):
    run = entry['run']
    if run['exit'] is not None:
        return 'exit'
    root = next((f for f in run['fibers'] if f['id'] == 0), None)
    return 'parked' if root is not None and root['parkedToken'] is not None else 'frontier'


def run_outcome(row):
    notes = ' '.join(row['notes'])
    if row['exitAgree'] is None and 'printer refused' in notes:
        return 'refused-by-printer'
    if row['hostExit'].startswith('module failed to load') or row['hostExit'].startswith('main is not an Effect'):
        return 'host-load-error'
    if row['exitAgree']:
        if 'both park' in notes:
            return 'both-park'
        return 'agree' if row['scheduleAgree'] else 'schedule-differs'
    if 'rc.112 parks, Lean settles' in notes:
        return 'host-timeout'
    if 'compile frontier' in notes:
        return 'lean-frontier'
    return 'differ'


def types_outcome(observation):
    if observation is None:
        return 'untyped'
    if observation['status'] == 'agree':
        return 'agree'
    if observation['status'] == 'refused':
        return 'refused'
    axes = [axis for axis, column in observation['columns'].items()
            if column['actualToExpected'] is False or column['expectedToActual'] is False]
    return 'mismatch-' + ','.join(axes)


def lean_text(entry):
    exit = entry['run']['exit']
    if exit is None:
        return verdict(entry)
    return cell(json.dumps(exit, separators=(',', ':')))


def cell(text):
    return re.sub(r'\s+', ' ', str(text)).strip()


def main():
    promote = '--promote' in sys.argv
    bun, modules, host_path = truth_host.select(root, truth)
    if WORK.exists():
        shutil.rmtree(WORK)
    (WORK / 'generated').mkdir(parents=True)
    shutil.copyfile(truth / 'prelude.ts', WORK / 'prelude.ts')
    # The prelude imports the session boundary by a relative path, as the truth check copies it.
    shutil.copytree(truth / 'session', WORK / 'session', ignore=shutil.ignore_patterns('.work'))

    manifest = WORK / 'corpus.json'
    subprocess.run(['lake', 'env', 'lean', '-M4096', '--run', 'harness/truth/Truth.lean', '--corpus',
                    str(manifest), str(COUNT), str(DEPTH)], cwd=root, check=True, timeout=3600)
    entries = {e['name']: e for e in json.loads(manifest.read_text())['programs']}

    # One process per program, with a kill timeout: a printed program can loop forever on
    # rc.112 inside a synchronous loop, which no in-process deadline interrupts (the first
    # corpus run found `g28`, an ill-typed `whileLoop` whose test is the number 1). Only
    # well-typed programs with a Lean verdict are run: the run comparison is a claim about
    # programs the rules admit, and a Lean frontier has no verdict to compare.
    rows, hung = {}, set()
    for name, entry in entries.items():
        if not entry['wellTyped'] or verdict(entry) == 'frontier':
            continue
        for stale in ('result.json', 'result.md'):
            (WORK / stale).unlink(missing_ok=True)
        try:
            ran = subprocess.run([bun, 'run', host_path(truth / 'run-truth.ts'), '--manifest', host_path(manifest),
                                  '--out', host_path(WORK), '--timeout', str(TIMEOUT_MS), '--only', name,
                                  '--tape-out', host_path(WORK / 'tapes')],
                                 cwd=root, text=True, capture_output=True, timeout=PROGRAM_TIMEOUT_S)
        except subprocess.TimeoutExpired:
            hung.add(name)
            continue
        if ran.returncode not in (0, 1) or not (WORK / 'result.json').is_file():
            sys.exit(f'FAIL corpus: the runner did not complete on {name} (exit {ran.returncode}):\n'
                     f'{ran.stdout[-3000:]}{ran.stderr[-3000:]}')
        for row in json.loads((WORK / 'result.json').read_text())['rows']:
            rows[row['program']] = row

    config = json.loads((truth / 'tsconfig.json').read_text())
    config['include'] = ['generated']
    config.pop('files', None)
    (WORK / 'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
    typed = subprocess.run([bun, host_path(modules / 'typescript/bin/tsc'), '--pretty', 'false', '--noEmit',
                            '-p', host_path(WORK / 'tsconfig.json')],
                           cwd=WORK, text=True, capture_output=True, timeout=3600)
    with_errors = set()
    for line in typed.stdout.splitlines() + typed.stderr.splitlines():
        found = re.match(r'^(?:.*[/\\])?(g\d+)\.ts\(\d+,\d+\): error', line)
        if found:
            with_errors.add(found.group(1))

    types_report = WORK / 'types.json'
    subprocess.run([bun, host_path(root / 'tools/target/corpus.ts'), '--repo', str(root), '--manifest', str(manifest),
                    '--generated', str(WORK / 'generated'), '--out', str(types_report)],
                   cwd=root, check=True, timeout=3600)
    observations = {o['id'].removeprefix('program/'): o
                    for o in json.loads(types_report.read_text())['observations']}

    lines = ['\t'.join(COLUMNS)]
    counts = {'run': {}, 'types': {}, 'straight': 0}
    disagreements = []
    for name in sorted(entries, key=lambda n: int(n[1:])):
        entry, row = entries[name], rows.get(name)
        if not entry['wellTyped']:
            run = 'untyped'
        elif verdict(entry) == 'frontier':
            run = 'lean-frontier'
        elif name in hung:
            run = 'host-hang'
        else:
            run = run_outcome(row) if row else 'not-run'
        types = types_outcome(observations.get(name)) if entry['wellTyped'] else 'untyped'
        counts['run'][run] = counts['run'].get(run, 0) + 1
        counts['types'][types] = counts['types'].get(types, 0) + 1
        counts['straight'] += entry['straight']
        if run in DISAGREEMENTS or types.startswith('mismatch'):
            disagreements.append(name)
        lines.append('\t'.join([
            name, 'yes' if entry['straight'] else 'no', 'yes' if entry['wellTyped'] else 'no',
            'errors' if name in with_errors else 'clean', run,
            cell(row['leanExit']) if row else lean_text(entry),
            cell(row['hostExit']) if row else ('no exit within %ds (killed)' % PROGRAM_TIMEOUT_S if name in hung else 'not run'),
            types, cell('; '.join(row['notes'])) if row else '']))
    fresh = '\n'.join(lines) + '\n'
    (WORK / 'corpus-results.tsv').write_text(fresh)

    known = set(re.findall(r'`(g\d+)`', KNOWN.read_text())) if KNOWN.is_file() else set()
    unregistered = [n for n in disagreements if n not in known]
    print(f"corpus: {len(entries)} programs, {counts['straight']} in the straight-line fragment; "
          f"run {counts['run']}; types {counts['types']}")
    if promote:
        EXPECTED.write_text(fresh)
        print(f'promoted {EXPECTED.relative_to(root)}')
        if unregistered:
            print(f'{len(unregistered)} disagreement(s) not listed in {KNOWN.relative_to(root)}: {" ".join(unregistered)}')
        return 0
    if not EXPECTED.is_file():
        sys.exit(f'FAIL corpus: {EXPECTED.relative_to(root)} is missing; run `make gen-corpus-results` and review it')
    committed = EXPECTED.read_text()
    if committed != fresh:
        diff = difflib.unified_diff(committed.splitlines(), fresh.splitlines(),
                                    'committed', 'fresh', lineterm='', n=0)
        sys.exit('FAIL corpus: the fresh run differs from harness/truth/corpus-results.tsv; review, then '
                 '`make gen-corpus-results`:\n' + '\n'.join(list(diff)[:80]))
    if unregistered:
        sys.exit(f'FAIL corpus: {len(unregistered)} disagreement(s) with rc.112 or tsc are not listed in '
                 f'{KNOWN.relative_to(root)}: {" ".join(unregistered)}')
    print(f'PASS corpus: {len(entries)} programs match the committed results; '
          f'{len(disagreements)} registered disagreement(s)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
