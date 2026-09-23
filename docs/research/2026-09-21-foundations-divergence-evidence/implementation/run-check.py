#!/usr/bin/env python3
"""Capture a packet check with its exact command and exit status, without overwriting logs."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
root = Path.cwd()
evidence = Path(__file__).resolve().parent
label, *command = sys.argv[1:]
log = evidence / (label + '.log')
if log.exists():
    raise SystemExit('Refusing to overwrite ' + str(log))
started = time.time()
print('RUN ' + ' '.join(command), flush=True)
with log.open('w') as out:
    result = subprocess.run(command, cwd=root, env={**os.environ, 'LEAN_NUM_THREADS': '1'},
                            stdout=out, stderr=subprocess.STDOUT)
row = {'cwd': str(root), 'command': command, 'LEAN_NUM_THREADS': '1',
       'exit': result.returncode, 'elapsed_seconds': round(time.time() - started, 2), 'log': log.name}
with (evidence/'commands.jsonl').open('a') as out:
    out.write(json.dumps(row) + '\n')
print(json.dumps(row), flush=True)
raise SystemExit(result.returncode)
