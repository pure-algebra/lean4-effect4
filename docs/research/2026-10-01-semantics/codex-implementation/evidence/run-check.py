import os,sys,subprocess,time,json,pathlib,signal
b=pathlib.Path(__file__).parent
label=sys.argv[1]; cmd=sys.argv[2:]
env={**os.environ,'LEAN_NUM_THREADS':'1','GOMAXPROCS':'1','GOMEMLIMIT':'512MiB'}
if label.startswith('prepare'):
 env.update(LAKE_OVERRIDE_LEAN='true',LEAN_SYSROOT=str(b/'serial-toolchain'))
start=time.monotonic()
with (b/(label+'.log')).open('w') as log:
 p=subprocess.Popen(cmd,cwd='/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 try: p.wait(timeout=900)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGTERM); p.wait(timeout=10)
receipt={'command':cmd,'exit':p.returncode,'elapsed':round(time.monotonic()-start,3)}
(b/(label+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt)); print('\n'.join((b/(label+'.log')).read_text().splitlines()[-25:]))
sys.exit(p.returncode)
