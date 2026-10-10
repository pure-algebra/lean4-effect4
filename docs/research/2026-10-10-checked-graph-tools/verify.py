"""Run narrow graph-tool checks serially, retaining commands and measured results."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORT = HERE / 'verification.json'
ENV = {**os.environ, 'LEAN_NUM_THREADS': '3'}
PRODUCTION = [
    'tools/Tools/Graph/Path.lean', 'tools/Tools/View/Flow.lean',
    'tools/Tools/View/FlowLaws.lean', 'tools/Tools/View/FlowPath.lean',
]

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def lean(file):
    return ['lake', 'env', 'sh', '-c',
        'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$2" "$3"',
        'graph-tools-check', str(HERE), str(HERE / (file[:-5] + '.olean')), str(HERE / file)]

jobs = [('narrow-build', ['lake', 'build', 'Tools.View.FlowPath', 'Tools.View.FlowOrder',
    'Tools.View.FlowSpecimen', 'Tools.View.Build'])]
jobs += [(p[:-5], lean(p)) for p in [
    'Baseline.lean', 'PathControls.lean', 'PlacementControls.lean',
    'FlowPathControls.lean', 'ProofPathControls.lean', 'Reuse.lean']]
selected = set(sys.argv[1:])
record = json.loads(REPORT.read_text()) if selected and REPORT.exists() else {'checks': {}}
record.update({
    'base': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'lean_num_threads': 3,
    'scope': 'Narrow local proofs, finite controls, and compiled call structure. No full sweep or host equivalence.',
})
for name, command in jobs:
    if selected and name not in selected:
        continue
    before = {p: digest(ROOT / p) for p in PRODUCTION}
    started = time.monotonic()
    log = HERE / (name + '.log')
    print('Checking ' + name, flush=True)
    with log.open('w') as out:
        result = subprocess.run(command, cwd=ROOT, env=ENV, stdout=out, stderr=subprocess.STDOUT)
    stable = before == {p: digest(ROOT / p) for p in PRODUCTION}
    item = {
        'command': command, 'exit_code': result.returncode,
        'elapsed_seconds': round(time.monotonic() - started, 3),
        'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'production_sha256': before, 'production_stable': stable,
        'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
    }
    probe = HERE / (name + '.lean')
    if probe.exists(): item['probe_sha256'] = digest(probe)
    record['checks'][name] = item
    record['all_passed'] = len(record['checks']) == len(jobs) and all(
        c['exit_code'] == 0 and c['production_stable'] for c in record['checks'].values())
    REPORT.write_text(json.dumps(record, indent=2) + '\n')
    if result.returncode or not stable:
        print(log.read_text()[-8000:])
        raise SystemExit(result.returncode or 1)
print('PASS: requested narrow graph-tool checks', flush=True)
