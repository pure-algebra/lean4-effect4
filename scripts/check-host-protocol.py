#!/usr/bin/env python3
"""Fresh T-09/T-12 projection, typed host execution, checked replay, and mutation gate.
Every run regenerates small fixtures. The generated host programs and the adapter sources are
type-checked by tsgo 7 (the pinned `@typescript/native-preview`, run under node as `check-target`
runs it); `tsc` and `typescript@5.x` are never run (AGENTS.md, owner 2026-09-18 and 2026-10-01).

The lane also holds the host half of the dogfood scenarios (decisions row 254). Lean writes one
fixture for each script of a battery that a host can perform. The runner performs each script
on its printed module, and Lean replays each recording. Every written module is type-checked,
under each header that the runner writes for it.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import sys

ROOT = Path(__file__).resolve().parent.parent
SESSION = ROOT / 'harness/truth/session'
MODULES = ROOT / 'ts/eff/node_modules'
TSGO = MODULES / '@typescript/native-preview/bin/tsgo'
# The scenarios' batteries, which `Keyed.lean` imports, and the one tool module beside them.
SCENARIOS = ['Test.Dogfood.Scenario.Routing', 'Tools.ProfileJson']
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

def lean(path, *args, output=None):
    run('lake', 'env', 'lean', '-DwarningAsError=true', '-M4096', '--run', path,
        *map(str, args), output=output)

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
        # Include the actual generated expressions, alongside every owned adapter source.
        config = {'extends': str(ROOT / 'harness/truth/tsconfig.json'),
                  'include': [str(host / '*.ts'), str(SESSION / '*.ts')],
                  'compilerOptions': {'types': ['bun'], 'typeRoots': [str(MODULES / '@types')]}}
        (work / 'tsconfig.json').write_text(json.dumps(config))
        run(node, str(TSGO), '--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json'))
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
        # Explicit legacy adapter remains buildable; no stale, deleted library import.
        lean('harness/truth/session/Session.lean', 'emit', output=work / 'legacy-fixtures.json')
        latest = work_root / 'latest'
        if latest.exists():
            shutil.rmtree(latest)
        shutil.copytree(work, latest)
    print('PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls; '
          'the scenarios\' scripts on their printed modules')

if __name__ == '__main__':
    main()
