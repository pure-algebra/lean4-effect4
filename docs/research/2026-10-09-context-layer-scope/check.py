"""Check the retained source with its frozen dependency artifacts, one Lean process at a time."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

receipt = Path(__file__).resolve().parent
root = receipt.parents[2]
overlay = root / '.lake/context-layer-scope'
logs = receipt / 'checks'
logs.mkdir(exist_ok=True)
pins = json.loads((receipt / 'pins.json').read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for source in pins['sources']:
    path = receipt / 'snapshot' / source['path']
    if digest(path) != source['sha256']:
        raise SystemExit(f'Retained source changed: {path}')
for artifact in pins['artifacts']:
    if artifact['module'] == 'Effect4.Program.Compile':
        continue  # This module is recompiled below from retained source.
    path = root / artifact['target']
    if not path.is_file() or digest(path) != artifact['sha256']:
        raise SystemExit(f'Frozen dependency missing or changed: {path}')

metadata = {
    'started_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'lean_toolchain': (root / 'lean-toolchain').read_text().strip(),
    'controls_sha256': digest(receipt / 'Controls.lean'),
    'check_script_sha256': digest(Path(__file__)),
    'pins_sha256': digest(receipt / 'pins.json'),
    'input_hashes_match': True,
    'dependency_sources_rebuilt': False,
}
(logs / 'validation.json').write_text(json.dumps(metadata, indent=2) + '\n')

env = {**os.environ, 'LEAN_NUM_THREADS': '3'}
prefix = [
    'lake', 'env', 'bash', '-c',
    'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"',
    'review', str(overlay), '-DwarningAsError=true',
]
jobs = [
    ('Compile', prefix + [
        '--root=' + str(receipt / 'snapshot/src'), '-o',
        str(overlay / 'Effect4/Program/Compile.olean'),
        str(receipt / 'snapshot/src/Effect4/Program/Compile.lean'),
    ]),
    ('Controls', prefix + ['--run', str(receipt / 'Controls.lean')]),
]
results = []
for name, command in jobs:
    print('CHECK', name, flush=True)
    result = subprocess.run(
        command, cwd=root, env=env, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (logs / (name + '.log')).write_text(result.stdout)
    results.append({'name': name, 'command': command, 'exit_code': result.returncode})
    (logs / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(result.stdout, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
