#!/usr/bin/env python3
"""Keep exact command receipts for the requested seams worktree."""
import datetime
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[4]
slice_name, label, *command = sys.argv[1:]
directory = root / 'docs/research/2026-10-17-seams/receipts/evidence' / slice_name
directory.mkdir(parents=True, exist_ok=True)
log = directory / (label + '.log')
start = time.monotonic()
record = {'command': command, 'cwd': str(root), 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
with log.open('w') as out:
    out.write(json.dumps(record) + '\n')
    out.flush()
    result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT, env={**os.environ, 'LEAN_NUM_THREADS': '3'})
record.update(exit_status=result.returncode, elapsed_seconds=round(time.monotonic()-start, 3), log=str(log.relative_to(root)))
(directory / (label + '.json')).write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
print('\n'.join(log.read_text().splitlines()[-35:]), flush=True)
sys.exit(result.returncode)
