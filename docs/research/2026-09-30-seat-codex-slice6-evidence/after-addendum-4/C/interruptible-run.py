import os, pathlib, subprocess, sys, time
ROOT=pathlib.Path('/Users/pooks/Dev/lean4-effect4-slice6')
HERE=ROOT/'docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/C'
name=sys.argv[1]; cmd=sys.argv[2:]
(HERE/(name+'.command.txt')).write_text(repr(cmd)+'\n')
start=time.monotonic()
with (HERE/(name+'.log')).open('w') as log:
    try:
        result=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT)
        code=result.returncode
    except KeyboardInterrupt:
        code=130
(HERE/(name+'.result.txt')).write_text(f'exit={code} elapsed_seconds={time.monotonic()-start:.2f}\n')
print(name,'exit',code,flush=True)
raise SystemExit(code)
