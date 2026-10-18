"""Serialized review probes and a source-tree fingerprint; no production writes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path('/Users/pooks/Dev/lean4-effect4')
HERE = Path(__file__).resolve().parent


def git(*args):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(ROOT), *args])


def snapshot():
    digest = hashlib.sha256()
    paths = sorted(p for p in git('ls-files', '-z').split(b'\0') if p)
    for raw in paths:
        p = ROOT / os.fsdecode(raw)
        data = os.readlink(p).encode() if p.is_symlink() else p.read_bytes() if p.is_file() else b'<absent>'
        digest.update(raw + b'\0' + hashlib.sha256(data).digest())
    inputs = sorted((HERE.parent).glob('*.md')) + sorted((HERE.parent/'designs').glob('*.md'))
    inputs += [ROOT/p for p in [
        'docs/research/2026-10-17-session-composition/plan.md',
        'docs/research/2026-10-17-session-composition/ledger.md',
        'docs/research/2026-10-17-session-composition/codex-review.md',
        'docs/research/2026-10-17-authoring-and-store/README.md',
        'docs/research/2026-10-17-ocaml-estate-review/cas/README.md',
        'docs/research/2026-10-17-ocaml-estate-review/plan.md',
    ]]
    return {
        'head': git('rev-parse', 'HEAD').decode().strip(),
        'branch': git('branch', '--show-current').decode().strip(),
        'status': git('status', '--short', '--untracked-files=all').decode(),
        'tracked_paths': len(paths), 'tracked_bytes_sha256': digest.hexdigest(),
        'diff_sha256': hashlib.sha256(git('diff', 'HEAD', '--binary')).hexdigest(),
        'inputs': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs if p.name != 'codex-review.md' or p.parent != HERE.parent},
    }


if sys.argv[1:] == ['baseline']:
    data = snapshot()
    (HERE/'baseline.json').write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='inputs'}, indent=2))
    sys.exit(0)

if sys.argv[1:] == ['unchanged']:
    before = json.loads((HERE/'baseline.json').read_text())
    after = snapshot()
    checks = {k: before[k] == v for k,v in after.items()}
    (HERE/'unchanged.json').write_text(json.dumps({'checks':checks,'after':after}, indent=2)+'\n')
    print(json.dumps(checks, indent=2))
    sys.exit(int(not all(checks.values())))

jobs = ['SeamsProtocolControls', 'SeamsCheckingControls', 'SeamsStoreControls', 'SeamsMirrorControls']
results = []
for name in jobs:
    if sys.argv[1:] and name not in sys.argv[1:]:
        continue
    source = HERE/(name+'.lean')
    logpath = HERE/(name+'.log')
    cmd = [str(ROOT/'scratch/lean-slot.sh'), 'env', 'LEAN_NUM_THREADS=3', 'lake', 'env', 'lean', '-DwarningAsError=true', str(source)]
    started = datetime.now(timezone.utc).isoformat()
    with logpath.open('w') as log:
        run = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    row = {'probe':name, 'cwd':str(ROOT), 'command':cmd, 'started_utc':started, 'exit':run.returncode,
           'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
           'log':str(logpath), 'log_sha256':hashlib.sha256(logpath.read_bytes()).hexdigest()}
    results.append(row)
    print(json.dumps(row), flush=True)
    if run.returncode:
        print(logpath.read_text(), flush=True)
path = HERE/'results.json'
old = json.loads(path.read_text()) if path.exists() else []
rerun = {r['probe'] for r in results}
path.write_text(json.dumps([r for r in old if r['probe'] not in rerun]+results, indent=2)+'\n')
sys.exit(int(any(r['exit'] for r in results)))
