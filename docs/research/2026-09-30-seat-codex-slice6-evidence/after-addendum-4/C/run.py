import os, pathlib, subprocess, sys, time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[4]
name=sys.argv[1]
cmd=sys.argv[2:]
(HERE/(name+".command.txt")).write_text(repr(cmd)+"\n")
start=time.monotonic()
with (HERE/(name+".log")).open("w") as log:
 result=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_NUM_THREADS="1"),stdout=log,stderr=subprocess.STDOUT)
(HERE/(name+".result.txt")).write_text(f"exit={result.returncode} elapsed_seconds={time.monotonic()-start:.2f}\n")
print(name,"exit",result.returncode,flush=True)
raise SystemExit(result.returncode)
