#!/usr/bin/env python3
"""Check the retained review probes and audit their temporary Lean modules."""
from pathlib import Path
import hashlib
import json
import os
import shlex
import subprocess
import tempfile

probe_dir = Path(__file__).resolve().parent
repo = probe_dir.parents[3]
probe_rel = probe_dir.relative_to(repo)
slot = '/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh'
names = ['CodexRelations', 'CodexInline', 'CodexObjects', 'CodexClosure']
receipt = {'source_head': subprocess.check_output(
    ['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(), 'checks': []}
manifest = json.loads((repo / 'lake-manifest.json').read_text())
for package in manifest['packages']:
    folder = repo / '.lake/packages' / package['name']
    actual = subprocess.check_output(['git', '-C', str(folder), 'rev-parse', 'HEAD'],
                                    cwd=repo, text=True).strip()
    if actual != package['rev']:
        raise SystemExit(f"Package pin mismatch: {package['name']}")
receipt['packages'] = {p['name']: p['rev'] for p in manifest['packages']}


def check(name, command, env=None):
    result = subprocess.run(command, cwd=repo, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (probe_dir / (name + '.log')).write_text(result.stdout)
    source = probe_dir / (name + '.lean')
    entry = {'file': str(source.relative_to(repo)),
             'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
             'command': shlex.join(command), 'exit': result.returncode,
             'output': str((probe_dir / (name + '.log')).relative_to(repo))}
    if env is not None:
        entry['LEAN_PATH'] = env['LEAN_PATH']
    receipt['checks'].append(entry)
    (probe_dir / 'CodexCheck.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'{name}: exit {result.returncode}', flush=True)
    if result.returncode:
        print(result.stdout, flush=True)
        raise SystemExit(result.returncode)


with tempfile.TemporaryDirectory(prefix='proc-close-review-', dir='/private/tmp') as scratch:
    for name in names:
        check(name, [slot, 'lake', 'env', 'lean', '-DwarningAsError=true',
                     '--root=' + str(probe_rel), '-o', str(Path(scratch) / (name + '.olean')),
                     str(probe_rel / (name + '.lean'))])
    environment = os.environ.copy()
    previous = environment.get('LEAN_PATH', '')
    environment['LEAN_PATH'] = scratch + (os.pathsep + previous if previous else '')
    check('CodexAudit', [slot, 'lake', 'env', 'lean', '-DwarningAsError=true',
                         str(probe_rel / 'CodexAudit.lean')], environment)
