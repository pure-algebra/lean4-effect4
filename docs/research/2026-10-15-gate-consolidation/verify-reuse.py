from pathlib import Path
import json, os, subprocess, time

root = Path('/home/kokok/Dev/lean4-effect4-gates-dev')
os.environ['LEAN_NUM_THREADS'] = '3'
rows = []

def run(name, target):
    started = time.monotonic()
    command = ['make', '--no-print-directory', target]
    with (root / f'scratch/{name}.log').open('w') as log:
        result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
    row = {'name': name, 'command': command, 'seconds': round(time.monotonic()-started, 3), 'exit': result.returncode}
    rows.append(row)
    (root / 'scratch/reuse-gates.json').write_text(json.dumps(rows, indent=2)+'\n')
    print(json.dumps(row), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return (root / f'scratch/{name}.log').read_text()

proof = root / 'src/Effect4/Laws/Api/Runner.lean'
original = proof.read_bytes()
try:
    proof.write_bytes(original + b'\n-- Proof-only content-key isolation probe.\n')
    output = run('proof-edit', 'check-ocaml')
    assert ': recorded ' not in output, output
finally:
    proof.write_bytes(original)

run('clean-local-markers', 'clean-check')
output = run('clean-reuse', 'check-full')
assert ': recorded ' not in output, output
assert 'bun install' not in output, output
assert 'scripts/generate.py --only' not in output, output
run('final-status', 'status')
