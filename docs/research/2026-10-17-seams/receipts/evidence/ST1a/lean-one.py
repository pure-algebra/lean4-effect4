#!/usr/bin/env python3
"""Serialize this goal's Lean commands before entering the shared launcher."""
import fcntl
import os
from pathlib import Path
import subprocess
import sys

guard = Path('/private/tmp/effect4-seams-single-lean.lock')
with guard.open('a') as lock:
    fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
    command = ['/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh',
               'env', 'LEAN_NUM_THREADS=3', *sys.argv[1:]]
    result = subprocess.run(command, env={**os.environ, 'LEAN_NUM_THREADS': '3'})
    raise SystemExit(result.returncode)
