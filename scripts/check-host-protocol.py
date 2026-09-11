#!/usr/bin/env python3
"""Fresh T-09/T-12 projection, typed host execution, checked replay, and mutation gate.
Every run regenerates small fixtures. Large doc-example caching belongs to check-streams.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile
import sys

ROOT = Path(__file__).resolve().parent.parent
SESSION = ROOT / 'harness/truth/session'
MODULES = ROOT / 'ts/eff/node_modules'
sys.path.insert(0, str(ROOT / 'scripts/lib'))
from generated_bytes import comparable

def run(*args, output=None, timeout=180):
    if output:
        with output.open('w') as stream:
            subprocess.run(args, cwd=ROOT, check=True, stdout=stream, timeout=timeout)
    else:
        subprocess.run(args, cwd=ROOT, check=True, timeout=timeout)

def lean(path, *args, output=None):
    run('lake', 'env', 'lean', '-M4096', '--run', path, *map(str, args), output=output)

def main():
    bun = shutil.which('bun')
    if not bun or json.loads((MODULES / 'effect/package.json').read_text())['version'] != '4.0.0-rc.112':
        raise SystemExit('FAIL host-protocol: Bun and the pinned rc.112 installation are required')
    run('lake', 'build', 'Test.Api.HostSessionContract', 'Test.Api.KeyedHostContract', 'Test.Api.HostSessionAxiomReport')
    work_root = SESSION / '.work'
    work_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='check-', dir=work_root) as tmp:
        work = Path(tmp)
        projection = work / 'projection'
        lean('tools/Tools/HostProtocol.lean', projection)
        for name in ['protocol.gen.ts', 'tape.schema.json', 'tape.schema.json.cut-from']:
            if comparable((projection / name).read_bytes()) != comparable((SESSION / name).read_bytes()):
                raise SystemExit(f'FAIL host-protocol: {name} drift; run scripts/generate-host-protocol.sh')
        fixtures = work / 'fixtures.json'
        lean('harness/truth/session/Keyed.lean', 'emit', output=fixtures)
        host = work / 'host'
        run(bun, str(SESSION / 'run-keyed.ts'), str(fixtures), str(host))
        # Include the actual generated expressions, alongside every owned adapter source.
        config = {'extends': str(ROOT / 'harness/truth/tsconfig.json'),
                  'include': [str(host / '*.ts'), str(SESSION / '*.ts')],
                  'compilerOptions': {'types': ['bun'], 'typeRoots': [str(MODULES / '@types')]}}
        (work / 'tsconfig.json').write_text(json.dumps(config))
        run(bun, str(MODULES / 'typescript/bin/tsc'), '--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json'))
        run(bun, 'test', str(SESSION / 'keyed-protocol.test.ts'), str(SESSION / 'protocol.test.ts'), str(SESSION / 'resource.test.ts'))
        lean('harness/truth/session/Keyed.lean', 'batch', host / 'cases.json', output=work / 'lean.json')
        run(bun, str(SESSION / 'prepare-keyed-controls.ts'), str(host))
        lean('harness/truth/session/Keyed.lean', 'batch', host / 'controls.json', output=work / 'controls-lean.json')
        run(bun, str(SESSION / 'check-keyed.ts'), str(host), str(work / 'lean.json'), str(work / 'controls-lean.json'))
        # Explicit legacy adapter remains buildable; no stale, deleted library import.
        lean('harness/truth/session/Session.lean', 'emit', output=work / 'legacy-fixtures.json')
        latest = work_root / 'latest'
        if latest.exists():
            shutil.rmtree(latest)
        shutil.copytree(work, latest)
    print('PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls')

if __name__ == '__main__':
    main()
