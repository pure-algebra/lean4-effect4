import os, sys, subprocess, time, json, signal
from pathlib import Path

ROOT = Path('/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4')
OUT = Path(__file__).parent
TOOL = Path('/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
tag, seconds, *args = sys.argv[1:]
env = dict(os.environ, LEAN_NUM_THREADS='1')
cmd = [str(TOOL / 'lake'), 'env', str(TOOL / 'lean'), '-j1', '-M4096', '-DwarningAsError=true', *args]
start = time.monotonic()
with (OUT / (tag+'.log')).open('w') as log:
    p = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    try:
        code = p.wait(timeout=int(seconds))
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGTERM)
        p.wait(timeout=10)
        code = 124
result = dict(command=cmd, cwd=str(ROOT), exit=code, elapsed=round(time.monotonic()-start, 3), threads=1, memoryMiB=4096)
(OUT / (tag+'.json')).write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result))
print((OUT / (tag+'.log')).read_text()[-10000:])
sys.exit(code)
