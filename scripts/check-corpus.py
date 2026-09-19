#!/usr/bin/env python3
"""The generated corpus against rc.112 and the TypeScript compiler, one record per program.

`make check-corpus`. Five steps, then one expected file:

1. Lean writes the manifest of the generated corpus (`harness/truth/Truth.lean --corpus`,
   the 400 programs of `Test/Program/Gen.lean` at depth 4, each with its type, its printed
   module, the same module with no annotations, the machine's run and whether it is in the
   fragment `run_eq_meaning` covers).
2. The truth runner (`harness/truth/run-truth.ts --emit`) writes every printable program's
   modules under `harness/truth/corpus-check/`: `generated/<name>.ts` as shipped and
   `inferred/<name>.ts` with no annotations, with `emitted.json` saying what exists. Nothing
   is patched.
3. The runner runs each selected program on the pinned `effect@4.0.0-rc.112`, one process
   per program with a kill timeout, and compares rc.112's exit, schedule and synchronous
   exit with the machine's.
4. the one compiler (tsgo, decisions row 57) type-checks every emitted shipped module under
   the harness's compiler options; its column keeps the name `tsc`, which the register of
   known differences reads as a dimension.
5. `tools/target/corpus.ts` compares Lean's answer, error and requirement types with the
   types that compiler infers for the unannotated module, both assignment directions, on
   every well-typed program.

The result is `harness/truth/corpus-results.tsv`, one row per program: `straight`,
`wellTyped`, `module` (`decl` the shipped block, `expr` an ill-typed program's bare
expression, `refused` no module), `tsc` (`clean`, `errors`, `not-compiled`), `run`, `sync`,
Lean's exit, rc.112's exit, the two compared schedules in full, `types` and a note. The
committed file is the expected one: the check fails when a fresh run differs (the diff names
the programs) and when a row records a disagreement that
`harness/truth/corpus-known-differences.md` does not list for that program, dimension and
outcome, or lists one that no longer occurs. `--promote` writes the fresh file and reports
the unregistered and stale entries.

Only well-typed programs with a Lean verdict are run: the run comparison is a claim about
programs the rules admit, and a printed program can loop forever on rc.112 inside a
synchronous loop that no in-process deadline interrupts. Every printable program is emitted
and compiled: no program is reported compiler-clean without having been compiled.

Run outcomes: `agree` (exit and schedule), `schedule-differs`, `both-park` (neither face
settled within the deadline; reported, never counted as agreement), `host-timeout` (Lean
settles, rc.112 does not), `host-hang` (the process had to be killed), `untyped` (ill-typed in
Lean, not run), `lean-frontier` (the machine ran out of fuel, no verdict, not run),
`refused-by-printer`, `host-load-error`, `differ`. Sync outcomes: `agree`, `differs`, `n/a`.
Type outcomes: `agree`, `mismatch-<axes>`, `refused` (with the reason in the note),
`untyped`. A disagreement is a `run` outcome other than agreement, `sync differs`, a
`types mismatch`, or `tsc errors` on a well-typed program.
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
COLUMNS = ['name', 'straight', 'wellTyped', 'module', 'tsc', 'run', 'sync', 'lean', 'host',
           'leanSchedule', 'hostSchedule', 'types', 'note']
RUN_DISAGREEMENTS = {'differ', 'schedule-differs', 'host-timeout', 'host-hang', 'host-load-error'}
NO_MODULE = {'source': None, 'inferred': False, 'refusal': None}


# ---- the pure part: classification, registration, verdict ---------------------------------

def verdict(entry):
    run = entry['run']
    if run['exit'] is not None:
        return 'exit'
    root_fiber = next((f for f in run['fibers'] if f['id'] == 0), None)
    return 'parked' if root_fiber is not None and root_fiber['parkedToken'] is not None else 'frontier'


def run_outcome(row):
    notes = ' '.join(row['notes'])
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


def sync_outcome(row):
    agree = row.get('runSyncAgree')
    return 'n/a' if agree is None else ('agree' if agree else 'differs')


def types_outcome(observation):
    if observation is None:
        return 'untyped'
    if observation['status'] == 'agree':
        return 'agree'
    if observation['status'] == 'refused':
        return 'refused'
    # The target oracle owns the relation; a failed reverse E assignment can be
    # accepted program containment and must not become a second mismatch here.
    axes = [axis for axis, column in observation['columns'].items()
            if column['agreement'] == 'mismatch']
    return 'mismatch-' + ','.join(axes)


def types_reason(observation):
    """The refusal's reasons, by code, for the note (exact cases, not a count)."""
    if observation is None or observation['status'] != 'refused':
        return ''
    reasons = []
    for issue in observation['issues']:
        code = issue['code'] + ('/' + issue['axis'] if issue.get('axis') else '')
        if code not in reasons:
            reasons.append(code)
    first = observation['issues'][0]['message'] if observation['issues'] else ''
    return 'types refused: ' + ' '.join(reasons) + (': ' + first if first else '')


def compared_schedule(rows):
    """The schedule as the runner compares it: `scheduled` rows dropped, one comma-joined cell."""
    return ','.join(r for r in rows if not r.startswith('scheduled '))


def lean_text(entry):
    exit = entry['run']['exit']
    if exit is None:
        return verdict(entry)
    return cell(json.dumps(exit, separators=(',', ':')))


def cell(text):
    return re.sub(r'\s+', ' ', str(text)).strip()


def classify(entries, emitted, rows, hung, tsc_errors, observations):
    """One classified record per program, in corpus order. Pure.

    `entries`: the manifest's programs by name; `emitted`: `emitted.json`; `rows`: the runner's
    rows by program; `hung`: the programs whose process was killed; `tsc_errors`: the first
    compiler error by program; `observations`: the type oracle's observations by program.
    Every field is decided from what was observed: a missing module is `not-compiled`, never
    `clean`; a program the runner never reported is `not-run`, never an agreement.
    """
    records = []
    for name in sorted(entries, key=lambda n: int(n[1:])):
        entry, row = entries[name], rows.get(name)
        module = emitted.get(name, NO_MODULE)
        observation = observations.get(name) if entry['wellTyped'] else None
        if not entry['wellTyped']:
            run = 'untyped'
        elif module['source'] is None:
            run = 'refused-by-printer'
        elif verdict(entry) == 'frontier':
            run = 'lean-frontier'
        elif name in hung:
            run = 'host-hang'
        elif row is None:
            run = 'not-run'
        else:
            run = run_outcome(row)
        sync = sync_outcome(row) if row is not None else 'n/a'
        tsc = 'not-compiled' if module['source'] is None else ('errors' if name in tsc_errors else 'clean')
        types = types_outcome(observation) if entry['wellTyped'] else 'untyped'
        notes = []
        if module['source'] is None and module['refusal']:
            notes.append('printer refused: ' + module['refusal'])
        if row is not None:
            notes.extend(row['notes'])
        if name in tsc_errors:
            notes.append('tsc: ' + tsc_errors[name])
        reason = types_reason(observation)
        if reason:
            notes.append(reason)
        host = row['host'] if row is not None else None
        if row is not None:
            host_text = cell(row['hostExit'])
        elif name in hung:
            host_text = 'no exit within %ds (killed)' % PROGRAM_TIMEOUT_S
        else:
            host_text = 'not run'
        records.append({
            'name': name, 'straight': 'yes' if entry['straight'] else 'no',
            'wellTyped': 'yes' if entry['wellTyped'] else 'no',
            'module': module['source'] or 'refused', 'tsc': tsc, 'run': run, 'sync': sync,
            'lean': cell(row['leanExit']) if row is not None else lean_text(entry),
            'host': host_text,
            'leanSchedule': compared_schedule(entry['run']['schedule']) if entry['wellTyped'] else '',
            'hostSchedule': compared_schedule(host['schedule']) if host else '',
            'types': types, 'note': cell('; '.join(notes))})
    return records


def disagreements_of(records):
    """`(program, dimension, outcome)` for every recorded disagreement."""
    found = []
    for r in records:
        if r['run'] in RUN_DISAGREEMENTS:
            found.append((r['name'], 'run', r['run']))
        if r['sync'] == 'differs':
            found.append((r['name'], 'sync', 'differs'))
        if r['types'].startswith('mismatch'):
            found.append((r['name'], 'types', r['types']))
        if r['wellTyped'] == 'yes' and r['tsc'] == 'errors':
            found.append((r['name'], 'tsc', 'errors'))
    return found


def parse_register(text):
    """The registered `(program, dimension, outcome)` triples of the known-differences table:
    a table row lists its programs in backticks in the first column and `<dimension> <outcome>`
    in the second. Anything else on the page registers nothing."""
    registered = set()
    for line in text.splitlines():
        if not line.startswith('|'):
            continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if len(cells) < 3:
            continue
        found = re.fullmatch(r'(run|sync|types|tsc) (\S+)', cells[1])
        if found is None:
            continue
        for name in re.findall(r'`(g\d+)`', cells[0]):
            registered.add((name, found.group(1), found.group(2)))
    return registered


def render(records):
    lines = ['\t'.join(COLUMNS)]
    lines.extend('\t'.join(r[c] for c in COLUMNS) for r in records)
    return '\n'.join(lines) + '\n'


def counts(records):
    out = {'run': {}, 'sync': {}, 'types': {}, 'tsc': {}, 'straight': 0}
    for r in records:
        for key in ('run', 'sync', 'types', 'tsc'):
            out[key][r[key]] = out[key].get(r[key], 0) + 1
        out['straight'] += r['straight'] == 'yes'
    return out


def triple(t):
    return '%s %s %s' % t


def judge(fresh, committed, disagreements, registered):
    """The check's verdict: `(exit code, message)`. Drift first, then the register, both ways."""
    if committed is None:
        return 1, 'FAIL corpus: harness/truth/corpus-results.tsv is missing; run `make gen-corpus-results` and review it'
    if committed != fresh:
        diff = difflib.unified_diff(committed.splitlines(), fresh.splitlines(), 'committed', 'fresh', lineterm='', n=0)
        return 1, ('FAIL corpus: the fresh run differs from harness/truth/corpus-results.tsv; review, then '
                   '`make gen-corpus-results`:\n' + '\n'.join(list(diff)[:80]))
    unregistered = [t for t in disagreements if t not in registered]
    stale = sorted(registered - set(disagreements))
    if unregistered:
        return 1, ('FAIL corpus: %d disagreement(s) with rc.112 or tsc are not listed in harness/truth/corpus-known-differences.md '
                   'for their program, dimension and outcome: %s' % (len(unregistered), '; '.join(map(triple, unregistered))))
    if stale:
        return 1, ('FAIL corpus: %d entry(ies) of harness/truth/corpus-known-differences.md no longer occur; remove them: %s'
                   % (len(stale), '; '.join(map(triple, stale))))
    return 0, 'PASS corpus: %d programs match the committed results; %d registered disagreement(s)' % (
        len(fresh.splitlines()) - 1, len(disagreements))


# ---- the I/O part -------------------------------------------------------------------------

def main():
    promote = '--promote' in sys.argv
    bun, modules, host_path = truth_host.select(root, truth)
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir(parents=True)
    shutil.copyfile(truth / 'prelude.ts', WORK / 'prelude.ts')
    # The prelude re-exports the generated atom block beside it (make gen-derived), as the truth
    # check copies it. Without this copy every emitted module loses every atom: the one compiler
    # says so (TS2305 per program), the retired one reported only an unattributed module error
    # against the prelude, which this lane's per-program regex never saw.
    shutil.copyfile(truth / 'prelude-atoms.gen.ts', WORK / 'prelude-atoms.gen.ts')
    # The prelude imports the session boundary by a relative path, as the truth check copies it.
    shutil.copytree(truth / 'session', WORK / 'session', ignore=shutil.ignore_patterns('.work'))

    manifest = WORK / 'corpus.json'
    subprocess.run(['lake', 'env', 'lean', '-M4096', '--run', 'harness/truth/Truth.lean', '--corpus',
                    str(manifest), str(COUNT), str(DEPTH)], cwd=root, check=True, timeout=3600)
    entries = {e['name']: e for e in json.loads(manifest.read_text())['programs']}

    # Every printable program's modules, before any selection: what tsc compiles and what the
    # type oracle reads exist independently of which programs run.
    runner = [bun, 'run', host_path(truth / 'run-truth.ts'), '--manifest', host_path(manifest), '--out', host_path(WORK)]
    subprocess.run(runner + ['--emit'], cwd=root, check=True, text=True, timeout=600)
    emitted = json.loads((WORK / 'emitted.json').read_text())
    if set(emitted) != set(entries):
        sys.exit('FAIL corpus: the runner emitted an inventory for %d programs, the manifest names %d' % (len(emitted), len(entries)))

    # One process per program, with a kill timeout: a printed program can loop forever on
    # rc.112 inside a synchronous loop, which no in-process deadline interrupts (the first
    # corpus run found `g28`, an ill-typed `whileLoop` whose test is the number 1). Only
    # well-typed programs with a Lean verdict are run: the run comparison is a claim about
    # programs the rules admit, and a Lean frontier has no verdict to compare.
    rows, hung = {}, set()
    for name, entry in entries.items():
        if not entry['wellTyped'] or emitted[name]['source'] is None or verdict(entry) == 'frontier':
            continue
        for stale in ('result.json', 'result.md'):
            (WORK / stale).unlink(missing_ok=True)
        try:
            ran = subprocess.run(runner + ['--timeout', str(TIMEOUT_MS), '--only', name, '--tape-out', host_path(WORK / 'tapes')],
                                 cwd=root, text=True, capture_output=True, timeout=PROGRAM_TIMEOUT_S)
        except subprocess.TimeoutExpired:
            hung.add(name)
            continue
        if ran.returncode not in (0, 1) or not (WORK / 'result.json').is_file():
            sys.exit(f'FAIL corpus: the runner did not complete on {name} (exit {ran.returncode}):\n'
                     f'{ran.stdout[-3000:]}{ran.stderr[-3000:]}')
        reported = json.loads((WORK / 'result.json').read_text())['rows']
        if [r['program'] for r in reported] != [name]:
            sys.exit(f'FAIL corpus: the runner reported {[r["program"] for r in reported]} when asked for {name}')
        rows[name] = reported[0]

    config = json.loads((truth / 'tsconfig.json').read_text())
    config['include'] = ['generated']
    config.pop('files', None)
    (WORK / 'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
    typed = subprocess.run(truth_host.compiler(modules) + ['--pretty', 'false', '--noEmit',
                            '-p', host_path(WORK / 'tsconfig.json')],
                           cwd=WORK, text=True, capture_output=True, timeout=3600)
    tsc_errors = {}
    for line in typed.stdout.splitlines() + typed.stderr.splitlines():
        found = re.match(r'^(?:.*[/\\])?(g\d+)\.ts\(\d+,\d+\): (error TS\d+: .*)$', line)
        if found:
            tsc_errors.setdefault(found.group(1), found.group(2))
    if typed.returncode not in (0, 1, 2):
        sys.exit(f'FAIL corpus: tsc did not complete (exit {typed.returncode}):\n{typed.stdout[-3000:]}{typed.stderr[-3000:]}')

    types_report = WORK / 'types.json'
    subprocess.run([bun, host_path(root / 'tools/target/corpus.ts'), '--repo', str(root), '--manifest', str(manifest),
                    '--inferred', str(WORK / 'inferred'), '--out', str(types_report)],
                   cwd=root, check=True, timeout=3600)
    observations = {o['id'].removeprefix('program/'): o
                    for o in json.loads(types_report.read_text())['observations']}

    records = classify(entries, emitted, rows, hung, tsc_errors, observations)
    fresh = render(records)
    (WORK / 'corpus-results.tsv').write_text(fresh)
    disagreements = disagreements_of(records)
    registered = parse_register(KNOWN.read_text()) if KNOWN.is_file() else set()
    summary = counts(records)
    print(f"corpus: {len(records)} programs, {summary['straight']} in the straight-line fragment; "
          f"run {summary['run']}; sync {summary['sync']}; tsc {summary['tsc']}; types {summary['types']}")
    if promote:
        EXPECTED.write_text(fresh)
        print(f'promoted {EXPECTED.relative_to(root)}')
        unregistered = [t for t in disagreements if t not in registered]
        stale = sorted(registered - set(disagreements))
        if unregistered:
            print(f'{len(unregistered)} disagreement(s) not listed in {KNOWN.relative_to(root)}: '
                  + '; '.join(map(triple, unregistered)))
        if stale:
            print(f'{len(stale)} entry(ies) of {KNOWN.relative_to(root)} no longer occur: ' + '; '.join(map(triple, stale)))
        return 0
    code, message = judge(fresh, EXPECTED.read_text() if EXPECTED.is_file() else None, disagreements, registered)
    print(message)
    return code


if __name__ == '__main__':
    sys.exit(main())
