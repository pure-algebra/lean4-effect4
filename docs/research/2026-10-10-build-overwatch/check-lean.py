from pathlib import Path
import json,os,subprocess
r=Path(__file__).resolve().parent; root=r.parents[2]
overlay=root/".lake/build-overwatch"; results=[]
for name in ["TagOnly.lean","TagImports.lean","ImportControls.lean","CacheShapeControls.lean"]:
    cmd=["lake","env","bash","-c",'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"',"review",str(overlay),"-DwarningAsError=true",str(r/name)]
    p=subprocess.run(cmd,cwd=root,env={**os.environ,"LEAN_NUM_THREADS":"3"},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (r/"checks"/(name+".log")).write_text(p.stdout)
    results.append({"fixture":name,"command":cmd,"exit_code":p.returncode})
    (r/"checks/lean-controls.json").write_text(json.dumps(results,indent=2)+"\n")
    print(name,p.returncode,flush=True)
    if p.stdout: print(p.stdout,flush=True)
    if p.returncode: raise SystemExit(p.returncode)
