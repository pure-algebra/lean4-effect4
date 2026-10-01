import json, os, pathlib, subprocess, sys, time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[4]
name, relative_cwd, *cmd=sys.argv[1:]
cwd=ROOT/relative_cwd
record=dict(command=cmd,cwd=str(cwd),env=dict(LEAN_NUM_THREADS="1"))
(HERE/(name+".command.json")).write_text(json.dumps(record,indent=2)+"\n")
start=time.monotonic()
with (HERE/(name+".log")).open("w") as log:
 result=subprocess.run(cmd,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS="1"),stdout=log,stderr=subprocess.STDOUT)
record.update(exit=result.returncode,elapsed_seconds=round(time.monotonic()-start,2))
(HERE/(name+".result.json")).write_text(json.dumps(record,indent=2)+"\n")
print(name,"exit",result.returncode,flush=True)
raise SystemExit(result.returncode)
