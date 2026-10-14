#!/usr/bin/env python3
"""Fresh T-09/T-12 projection, typed host execution, checked replay, and mutation gate.
Every run regenerates small fixtures. The generated host programs and the adapter sources are
type-checked by tsgo 7 (the pinned `@typescript/native-preview`, run under node as `check-target`
runs it); `tsc` and `typescript@5.x` are never run (AGENTS.md, owner 2026-09-18 and 2026-10-01).

The lane also holds the host half of the dogfood scenarios (decisions row 254). Lean writes one
fixture for each script of a battery that a host can perform. The runner performs each script
on its printed module, and Lean replays each recording. Every written module is type-checked,
under each header that the runner writes for it.

The to-do's scripts run a second time on its emitted Effect service (decisions row 378 (20),
slice E4, `harness/truth/service/`). Lean writes the service's file into the to-do application's
folder (`apps/todo/`); tsgo 7 checks it with its consumer and red controls. The consumer's
programs perform each to-do script with the lane's recorder; Lean replays each recording and
decides each run's checks beside the script's own run.

The to-do application then runs on SQLite (decisions row 378 (16), slice V4, `apps/todo/`): its
front serves one script of requests from an empty database, over the shipped repository, two red
ones and a read-only one, and records each request. Lean rebuilds each request's run from its
record and decides its five checks (`apps/todo/Check.lean`), with three changed copies of the
shipped session.
"""
from pathlib import Path
import copy
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import sys

from generate import native_libraries

ROOT = Path(__file__).resolve().parent.parent
SESSION = ROOT / 'harness/truth/session'
# The to-do's emitted service (slice E4): its runner and red controls. The to-do application holds
# the file's writer, the consumer, and the work folder that the consumer imports the file from.
SERVICE = ROOT / 'harness/truth/service'
APP = ROOT / 'apps/todo'
SERVICE_FILE = APP / '.work'
MODULES = ROOT / 'ts/eff/node_modules'
TSGO = MODULES / '@typescript/native-preview/bin/tsgo'
# The scenarios' batteries, which `Keyed.lean` imports, and the one tool module beside them.
SCENARIOS = ['Test.Dogfood.Scenario.Workers', 'Test.Dogfood.Scenario.QueueWorkers',
             'Test.Dogfood.Scenario.Routing', 'Test.Dogfood.Scenario.Atomic',
             'Test.Dogfood.Scenario.Timeout', 'Test.Dogfood.Scenario.Todo.Claims',
             'Tools.ProfileJson']
# The recordings of the lane's four fixture families (two, shared, kv and the streams), as the
# runner wrote them at `310c8314`, before the scenarios came. A scenario's fixture is `scripted`,
# and a reader is off unless a scenario's fixture asks for it, so these bytes must not move.
# After a change of a family that is meant, pin the digest that the failure prints.
CASES_SHA256 = 'dca8595e99e85654328ad1560114f1885ff7efc2c132cb1b54c4e786757626c3'

def run(*args, output=None, timeout=180):
    if output:
        with output.open('w') as stream:
            subprocess.run(args, cwd=ROOT, check=True, stdout=stream, timeout=timeout)
    else:
        subprocess.run(args, cwd=ROOT, check=True, timeout=timeout)

# The shared libraries of the scenarios' modules, which `Keyed.lean` imports: `lean --run` then
# runs the machine as native code, where it interprets it otherwise (172 s for the scenarios'
# writer, against 14 s to 24 s native; `native_libraries`, `scripts/generate.py`).
LIBRARIES = []

def lean(path, *args, output=None):
    if not LIBRARIES:
        LIBRARIES.extend(native_libraries(SCENARIOS))
    run('lake', 'env', 'lean', '-DwarningAsError=true', '-M4096',
        *(f'--load-dynlib={library}' for library in LIBRARIES), '--run', path,
        *map(str, args), output=output)

def refused(node, project, expected):
    """tsgo 7 refuses a project of red controls with exactly the expected diagnostics, each a file
    and a code."""
    result = subprocess.run([node, str(TSGO), '--pretty', 'false', '--noEmit', '-p', str(project)],
                            cwd=ROOT, capture_output=True, text=True, timeout=180)
    found = {(line.split('(')[0], line.split(': error ')[1].split(':')[0])
             for line in result.stdout.splitlines() if ': error TS' in line}
    if result.returncode == 0 or found != expected:
        raise SystemExit(f'FAIL host-protocol: the red controls of {project} gave {sorted(found)}, '
                         f'and {sorted(expected)} is expected')

def check_service(fixtures, replays, decided):
    """Each to-do script performed on the emitted service replays in Lean to the script's
    observation and journal, and each run's checks (settled, conforming, the model's agreement)
    are the script's own. Answers the summary, or fails at the first disagreement."""
    if [entry['name'] for entry in replays] != fixtures:
        raise SystemExit('FAIL host-protocol: the service runs are not the to-do\'s scripts, once each')
    for entry in replays:
        result = entry['result']
        if 'refused' in result or not result.get('same') or not result.get('journal'):
            raise SystemExit(f'FAIL host-protocol: {entry["name"]} on the service does not replay as the script: {result}')
    if [entry['name'] for entry in decided['runs']] != fixtures or not decided['pairs']:
        raise SystemExit('FAIL host-protocol: the service checks do not cover the to-do\'s scripts and pairs')
    for entry in decided['runs']:
        if not entry['journal'] or entry['settled'] != entry['scriptedSettled'] or \
                entry['conforming'] != entry['scriptedConforming']:
            raise SystemExit(f'FAIL host-protocol: {entry["name"]} on the service is decided otherwise: {entry}')
    for pair in decided['pairs']:
        if pair['agrees'] != pair['scriptedAgrees']:
            raise SystemExit(f'FAIL host-protocol: the pair {pair["first"]}, {pair["second"]} agrees otherwise: {pair}')
    conforming = sum(entry['conforming'] for entry in decided['runs'])
    agreeing = sum(pair['agrees'] for pair in decided['pairs'])
    return (f'the to-do\'s service: {len(fixtures)} scripts on rc.112, each replayed to its journal; '
            f'{conforming} conform, {agreeing} of {len(decided["pairs"])} pairs agree with the model, as on the scripts')

def service_controls(fixtures, replays, decided):
    """Red controls of `check_service`: a replay off its script's journal, a run that conforms
    otherwise and a pair that agrees otherwise each fail it."""
    changes = [lambda r, d: r[0]['result'].update(journal=False),
               lambda r, d: d['runs'][0].update(conforming=not d['runs'][0]['conforming']),
               lambda r, d: d['pairs'][0].update(agrees=not d['pairs'][0]['agrees'])]
    for change in changes:
        changed_replays, changed_decided = copy.deepcopy(replays), copy.deepcopy(decided)
        change(changed_replays, changed_decided)
        try:
            check_service(fixtures, changed_replays, changed_decided)
        except SystemExit:
            continue
        raise SystemExit('FAIL host-protocol: a changed service decision passes the service checks')

# The checks that `apps/todo/Check.lean` decides of each request (the lowering note's §6.1).
CHECKS = ('built', 'replayed', 'exit', 'funded', 'atRest', 'hostDriven', 'conforming', 'agrees')

def failing(session):
    """The checks that fail on some request of a checked session."""
    return {check for request in session['requests'] for check in CHECKS if not request['verdict'][check]}

def tamper(app):
    """Three copies of the shipped repository's session, each changed at one record: the red
    control of one check each. An entry that the application does not hold fails `built`; a call's
    request that the program does not make fails `replayed`; an exit that the program does not
    reach fails `exit`. Answers each copy's name, the changed record's index and its check."""
    header, *lines = (app / 'sqlite.jsonl').read_text().splitlines()
    records = [json.loads(line) for line in lines]
    def write(name, index, change, check):
        changed = copy.deepcopy(records)
        change(changed[index])
        (app / f'{name}.jsonl').write_text('\n'.join([header, *map(json.dumps, changed)]) + '\n')
        return name, index, check
    called = next(index for index, record in enumerate(records)
                  if record['calls'] and isinstance(record['calls'][0]['request'], str))
    return [write('changed-entry', 0, lambda record: record.update(entry='purge'), 'built'),
            write('changed-request', called,
                  lambda record: record['calls'][0].update(request=record['calls'][0]['request'] + '!'), 'replayed'),
            write('changed-exit', len(records) - 1, lambda record: record.update(exit={'success': 'changed'}), 'exit')]

def failed_completions(path):
    """The calls of a session's file whose completion is a failure."""
    return [call for line in path.read_text().splitlines()[1:] for call in json.loads(line)['calls']
            if 'failure' in call['completion']]

def check_app(checked, tampered, failures):
    """The to-do on SQLite: every check of every request of the shipped repository's session
    passes; the forgetful repository fails `agrees` alone; the titleless one fails `conforming`, and
    nothing but `conforming` and `agrees`; the read-only one, whose `failures` SQLite answered,
    fails `agrees` alone, so each failure is the exit that Lean's run reaches; each changed copy
    fails its check at its record, and no request before that record fails. Answers the summary,
    or fails at the first finding."""
    shipped, forgetful, titleless, readonly, *copies = checked['sessions']
    if not shipped['requests'] or failing(shipped):
        raise SystemExit(f'FAIL host-protocol: the to-do on SQLite fails {sorted(failing(shipped))}')
    if failing(forgetful) != {'agrees'}:
        raise SystemExit(f'FAIL host-protocol: the forgetful repository fails {sorted(failing(forgetful))}, '
                         'and agrees alone is expected')
    if 'conforming' not in failing(titleless) or not failing(titleless) <= {'conforming', 'agrees'}:
        raise SystemExit(f'FAIL host-protocol: the titleless repository fails {sorted(failing(titleless))}, '
                         'and conforming is expected, with agrees at most')
    if not failures or failing(readonly) != {'agrees'}:
        raise SystemExit(f'FAIL host-protocol: the read-only repository, with {len(failures)} failed calls, '
                         f'fails {sorted(failing(readonly))}, and agrees alone is expected')
    if len(copies) != len(tampered):
        raise SystemExit('FAIL host-protocol: the checker did not answer each changed session')
    for session, (name, index, check) in zip(copies, tampered):
        requests = session['requests']
        if requests[index]['verdict'][check] or not all(request['verdict']['passed'] for request in requests[:index]):
            raise SystemExit(f'FAIL host-protocol: the changed session {name} does not fail {check} at its record {index}')
    name, index, check = tampered[-1]
    if failing(copies[-1]) != {check} or [i for i, r in enumerate(copies[-1]['requests']) if not r['verdict']['passed']] != [index]:
        raise SystemExit(f'FAIL host-protocol: the changed session {name} fails more than {check} at its record')
    return (f'the to-do on SQLite: {len(shipped["requests"])} requests from an empty database, each passing Lean\'s '
            f'five checks; the forgetful and titleless repositories fail agrees and conforming; '
            f'{len(failures)} writes that SQLite refused escape as the row\'s declared error; '
            f'{len(tampered)} changed records fail {", ".join(check for _, _, check in tampered)}')

def app_controls(checked, tampered, failures):
    """Red controls of `check_app`: a failing check of the shipped session, a forgetful session that
    agrees, a read-only session whose exit check fails, and a changed record that passes each fail
    it."""
    def fail_shipped(c):
        c['sessions'][0]['requests'][0]['verdict'].update(agrees=False, passed=False)
    def agree_forgetful(c):
        for request in c['sessions'][1]['requests']:
            request['verdict'].update(agrees=True, passed=True)
    def fail_readonly_exit(c):
        c['sessions'][3]['requests'][0]['verdict'].update(exit=False, passed=False)
    def pass_changed(c):
        c['sessions'][4]['requests'][tampered[0][1]]['verdict'].update(built=True, passed=True)
    for change in [fail_shipped, agree_forgetful, fail_readonly_exit, pass_changed]:
        changed = copy.deepcopy(checked)
        change(changed)
        try:
            check_app(changed, tampered, failures)
        except SystemExit:
            continue
        raise SystemExit('FAIL host-protocol: a changed verdict of the to-do on SQLite passes its checks')

def main():
    bun = shutil.which('bun')
    if not bun or json.loads((MODULES / 'effect/package.json').read_text())['version'] != '4.0.0-rc.112':
        raise SystemExit('FAIL host-protocol: Bun and the pinned rc.112 installation are required')
    # `bin/tsgo` is a node launcher of the native compiler; check-target runs it the same way.
    node = shutil.which('node')
    if not node or not TSGO.exists():
        raise SystemExit('FAIL host-protocol: node and the pinned @typescript/native-preview (tsgo) are required')
    for module in ['Test.Api.HostSessionContract', 'Test.Api.KeyedHostContract', *SCENARIOS]:
        run('lake', 'build', module)
    work_root = SESSION / '.work'
    work_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='check-', dir=work_root) as tmp:
        work = Path(tmp)
        projection = work / 'projection'
        lean('tools/Tools/HostProtocol.lean', projection)
        for name in ['protocol.gen.ts', 'tape.schema.json']:
            if (projection / name).read_bytes() != (SESSION / name).read_bytes():
                raise SystemExit(f'FAIL host-protocol: {name} drift; run make gen-host-protocol')
        fixtures = work / 'fixtures.json'
        lean('harness/truth/session/Keyed.lean', 'emit', output=fixtures)
        scenarios = work / 'scenarios.json'
        lean('harness/truth/session/Keyed.lean', 'scenarios', output=scenarios)
        host = work / 'host'
        run(bun, str(SESSION / 'run-keyed.ts'), str(fixtures), str(host), str(scenarios))
        digest = hashlib.sha256((host / 'cases.json').read_bytes()).hexdigest()
        if digest != CASES_SHA256:
            raise SystemExit('FAIL host-protocol: the recordings of the four fixture families moved: '
                             f'cases.json has the digest {digest}, and the pin is {CASES_SHA256}')
        # The to-do's service file, where its consumer imports it from (slice E4).
        lean('apps/todo/EmitTodo.lean', SERVICE_FILE, '../../../harness/truth/prelude.ts')
        # Include the actual generated expressions, alongside every owned adapter source, and the
        # service's consumer and runner with the file they import.
        config = {'extends': str(ROOT / 'harness/truth/tsconfig.json'),
                  'include': [str(host / '*.ts'), str(SESSION / '*.ts'), str(SERVICE / '*.ts'), str(APP / '*.ts')],
                  'compilerOptions': {'types': ['bun'], 'typeRoots': [str(MODULES / '@types')]}}
        (work / 'tsconfig.json').write_text(json.dumps(config))
        run(node, str(TSGO), '--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json'))
        # The consumer's red controls: each file fails with its one diagnostic.
        refused(node, SERVICE / 'red' / 'tsconfig.json',
                {('harness/truth/service/red/argument.ts', 'TS2345'),
                 ('harness/truth/service/red/unprovided.ts', 'TS2375')})
        run(bun, 'test', str(SESSION / 'keyed-protocol.test.ts'), str(SESSION / 'protocol.test.ts'), str(SESSION / 'resource.test.ts'), str(SESSION / 'clock.test.ts'))
        lean('harness/truth/session/Keyed.lean', 'batch', host / 'cases.json', output=work / 'lean.json')
        lean('harness/truth/session/Keyed.lean', 'scenario-batch', host / 'scenario-cases.json',
             output=work / 'scenario-lean.json')
        run(bun, str(SESSION / 'prepare-keyed-controls.ts'), str(host))
        lean('harness/truth/session/Keyed.lean', 'batch', host / 'controls.json', output=work / 'controls-lean.json')
        lean('harness/truth/session/Keyed.lean', 'scenario-batch', host / 'scenario-controls.json',
             output=work / 'scenario-controls-lean.json')
        run(bun, str(SESSION / 'check-keyed.ts'), str(host), str(work / 'lean.json'), str(work / 'controls-lean.json'),
            str(scenarios), str(work / 'scenario-lean.json'), str(work / 'scenario-controls-lean.json'))
        # The to-do's scripts on its emitted service (slice E4): performed on the consumer's
        # programs, replayed by Lean, and each run's checks decided beside the script's own.
        service = work / 'service'
        run(bun, '--no-install', str(SERVICE / 'run-todo.ts'), str(scenarios), str(service))
        lean('harness/truth/session/Keyed.lean', 'scenario-batch', service / 'service-cases.json',
             output=work / 'service-replay.json')
        lean('harness/truth/session/Keyed.lean', 'service-checks', service / 'service-cases.json',
             output=work / 'service-checks.json')
        todo = [fixture['name'] for fixture in json.loads(scenarios.read_text())['runs']
                if fixture['scenario'] == 'todo']
        replays = json.loads((work / 'service-replay.json').read_text())
        decided = json.loads((work / 'service-checks.json').read_text())
        served = check_service(todo, replays, decided)
        service_controls(todo, replays, decided)
        # The to-do application on SQLite (slice V4): the front serves the script over the shipped
        # repository, two red ones and a read-only one; Lean checks each session and three changed
        # copies of the shipped one.
        app = work / 'app'
        run(bun, '--no-install', str(APP / 'run.ts'), str(app))
        tampered = tamper(app)
        sessions = ['sqlite', 'forgetful', 'titleless', 'readonly', *(name for name, _, _ in tampered)]
        lean('apps/todo/Check.lean', *(app / f'{name}.jsonl' for name in sessions), output=work / 'app-checks.json')
        checked = json.loads((work / 'app-checks.json').read_text())
        failures = failed_completions(app / 'readonly.jsonl')
        applied = check_app(checked, tampered, failures)
        app_controls(checked, tampered, failures)
        # Explicit legacy adapter remains buildable; no stale, deleted library import.
        lean('harness/truth/session/Session.lean', 'emit', output=work / 'legacy-fixtures.json')
        latest = work_root / 'latest'
        if latest.exists():
            shutil.rmtree(latest)
        shutil.copytree(work, latest)
    print('PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls; '
          'the scenarios\' scripts on their printed modules; ' + served + '; ' + applied)

if __name__ == '__main__':
    main()
