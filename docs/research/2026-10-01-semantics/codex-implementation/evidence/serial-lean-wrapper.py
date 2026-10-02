#!/usr/bin/env python3
import fcntl, subprocess, sys, os, time, json
from pathlib import Path
base=Path('/private/tmp/codex-second-eyes-2026-10-01/semantics-implementation')
real='/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1'
with (base/'compiler.lock').open('w') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    start=time.time()
    args=sys.argv[1:]
    is_compile=any(a.endswith('.lean') for a in args)
    if is_compile: args += ['-j1','-M4096']
    with (base/'serial-processes.jsonl').open('a') as log: log.write(json.dumps({'event':'start','pid':os.getpid(),'time':start,'args':args})+'\n')
    try:
        code=subprocess.call([real+'/bin/lean',*args],env=dict(os.environ,LEAN_SYSROOT=real,LEAN_NUM_THREADS='1'),timeout=600)
    except subprocess.TimeoutExpired: code=124
    with (base/'serial-processes.jsonl').open('a') as log: log.write(json.dumps({'event':'end','pid':os.getpid(),'time':time.time(),'exit':code})+'\n')
    sys.exit(code)
