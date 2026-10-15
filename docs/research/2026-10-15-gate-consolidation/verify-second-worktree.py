from pathlib import Path
import json, os, shutil, subprocess, time

source = Path('/mnt/c/Users/kokok/.codex/worktrees/gates-consolidation/lean4-effect4')
root = Path('/home/kokok/Dev/lean4-effect4-gates-reuse')
dev = Path('/home/kokok/Dev/lean4-effect4-gates-dev')
os.environ['LEAN_NUM_THREADS'] = '3'
assert not (root / '.lake/build').exists(), 'The reuse tree must have no compiled project artifacts'
for name in json.loads((source / 'scratch/reuse-files.json').read_text(encoding='utf-8-sig')):
    target = root / name
    if (source / name).is_file():
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, target)
    else:
        target.unlink(missing_ok=True)
command = ['make', '--no-print-directory', 'check-native', 'check-compiler', 'check-schema-codec']
started = time.monotonic()
log = dev / 'scratch/second-worktree.log'
with log.open('w') as output:
    result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
output = log.read_text()
row = {'command': command, 'seconds': round(time.monotonic()-started, 3), 'exit': result.returncode,
       'compiled_project_artifacts': (root / '.lake/build').exists(),
       'shared_passes': output.count(': shared result '), 'new_passes': output.count(': recorded ')}
(dev / 'scratch/second-worktree.json').write_text(json.dumps(row, indent=2)+'\n')
print(json.dumps(row), flush=True)
assert result.returncode == 0, output
assert row['shared_passes'] == 3 and row['new_passes'] == 0, output
assert not row['compiled_project_artifacts'], output
