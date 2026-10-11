"""Compile a pinned proof-only overlay without changing the active checkout."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile

packet = Path(__file__).resolve().parent
repo = packet.parents[2]
commit = 'ec1cce6fa0e3cd62dee1c19c7230faa1aa16a13e'
overlay = Path(tempfile.mkdtemp(prefix='effect4-d1-review-'))
source = overlay / 'source'
# Lean selects the first root for a module prefix. Mirror that prefix so the
# pinned proof modules can still load the unchanged, built Tools dependencies.
base_tools = repo / '.lake/build/lib/lean/Tools'
for artifact in base_tools.rglob('*'):
    if artifact.is_file():
        link = overlay / artifact.relative_to(base_tools.parent)
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(artifact)

modules = ['AlgGraph', 'FlowLaws', 'FlowOrder']
manifest = {'dependencySourcePin': 'bfe97080657ecb87d4551fc8a4511580369f698d', 'commit': commit, 'sourceSha256': {}, 'commands': []}
env = dict(os.environ, LEAN_NUM_THREADS='3')
script = 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"'
for name in modules:
    relative = f'tools/Tools/View/{name}.lean'
    data = subprocess.check_output(['git', 'show', commit + ':' + relative], cwd=repo)
    manifest['sourceSha256'][relative] = hashlib.sha256(data).hexdigest()
    path = source / f'Tools/View/{name}.lean'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    target = overlay / f'Tools/View/{name}.olean'
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.is_symlink():
        target.unlink()
    cmd = ['lake', 'env', 'sh', '-c', script, 'lean-overlay', str(overlay),
           '-DwarningAsError=true', '--root=' + str(source), '-o', str(target), str(path)]
    result = subprocess.run(cmd, cwd=repo, env=env, capture_output=True, text=True)
    manifest['commands'].append({'module': name, 'argv': cmd, 'exitCode': result.returncode,
                                 'output': result.stdout + result.stderr})
    if result.returncode:
        (packet / 'build.json').write_text(json.dumps(manifest, indent=2) + '\n')
        raise SystemExit(result.stdout + result.stderr)
    print('Built pinned ' + name, flush=True)
cmd = ['lake', 'env', 'sh', '-c', script, 'lean-overlay', str(overlay), '-DwarningAsError=true', str(packet/'Probe.lean')]
result = subprocess.run(cmd, cwd=repo, env=env, capture_output=True, text=True)
(packet / 'output.txt').write_text(result.stdout + result.stderr)
manifest['probeCommand'] = cmd
manifest['probeExitCode'] = result.returncode
manifest['probeSha256'] = hashlib.sha256((packet/'Probe.lean').read_bytes()).hexdigest()
if not result.returncode:
    laws = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
    assert len(laws) == 12
    assert all(set(a.split(', ')) == {'propext', 'Quot.sound'} for _, a in laws)
    manifest['checkedLaws'] = [name for name, _ in laws]
    manifest['finiteControls'] = sum(line.startswith('#guard ') for line in (packet/'Probe.lean').read_text().splitlines())
(packet / 'build.json').write_text(json.dumps(manifest, indent=2) + '\n')
if result.returncode:
    raise SystemExit(result.stdout + result.stderr)
print('PASS pinned D1 compilation, trust inspection and direction controls', flush=True)
