from pathlib import Path
import json, os, subprocess, time

root = Path('/home/kokok/Dev/lean4-effect4-gates-dev')
source = Path('/mnt/c/Users/kokok/.codex/worktrees/gates-consolidation/lean4-effect4')
os.environ['LEAN_NUM_THREADS'] = '3'
rows = []
for name, target in [('full-final','check-full'), ('warm-final','check-full'), ('docs-final','check-docs')]:
    command = ['make', '--no-print-directory', target]
    started = time.monotonic()
    with (root / f'scratch/{name}.log').open('w') as log:
        result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
    row = {'name': name, 'command': command, 'seconds': round(time.monotonic()-started, 3), 'exit': result.returncode}
    rows.append(row)
    (root / 'scratch/final-behavior.json').write_text(json.dumps(rows, indent=2)+'\n')
    print(json.dumps(row), flush=True)
    if result.returncode: raise SystemExit(result.returncode)
subprocess.run(['python3', str(source / 'scratch/verify-reuse.py')], check=True)
subprocess.run(['python3', str(source / 'scratch/verify-second-worktree.py')], check=True)
