from pathlib import Path
import json,os,subprocess,sys
r=Path(__file__).resolve().parent;root=r.parents[2];logs=r/"checks";logs.mkdir(exist_ok=True)
base=["lake","env","bash","-c",'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"',"review",str(root/".lake/report-overwatch"),"-DwarningAsError=true"]
commands=[
 ("existing-controls",base+["--run",str(r/"snapshot/tools/Drivers/SemanticsControls.lean")],"PASS semantics controls:"),
 ("cache-controls",base+["--root="+str(r),str(r/"GraphControls.lean")],"PASS: cold/warm caches"),
 ("closure-controls",base+["--root="+str(r),"-c",str(logs/"ClosureControls.c"),str(r/"ClosureControls.lean")],"fixture ReviewClosure.rebuilt:")]
path=logs/"results.json"
results=json.loads(path.read_text()) if sys.argv[1:] and path.exists() else []
for name,command,expected in commands:
    if sys.argv[1:] and name not in sys.argv[1:]:continue
    print("CHECK "+name,flush=True)
    p=subprocess.run(command,cwd=root,env={**os.environ,"LEAN_NUM_THREADS":"3"},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logs/(name+".log")).write_text(p.stdout)
    matched=p.returncode==0 and expected in p.stdout
    results=[row for row in results if row["name"]!=name]+[{"name":name,"command":command,"exit_code":p.returncode,"matched":matched}]
    path.write_text(json.dumps(results,indent=2)+"\n")
    print(p.stdout,flush=True)
    print("PASS" if matched else "UNEXPECTED",flush=True)
    if not matched:raise SystemExit(1)
