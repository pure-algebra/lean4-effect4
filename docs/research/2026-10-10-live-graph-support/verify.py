#!/usr/bin/env python3
"""Run only the combined tool slice, serially, retaining exact evidence."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
ENV=dict(os.environ, LEAN_NUM_THREADS="3")
LOG=HERE/"integration"
LOG.mkdir(exist_ok=True)
R=HERE/"run-view"
def lean(path): return ["lake","env","lean","-DwarningAsError=true",str(path)]
def local_lean(name, output):
    return ["lake","env","sh","-c",'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$1/$2.olean" "$1/$2.lean"',"run-view",str(R),name]
jobs=[
 ("build",["lake","build","Tools.Session.Snapshot","Tools.View.FlowLaws","Tools.View.FlowPath","Tools.View.FlowOrder","Tools.View.Run","Tools.View.Build","Tools.View.Specimen","Tools.View.FlowSpecimen","Tools.View.Output","ProofGraph.AxiomAudit"]),
 ("snapshot",lean(HERE/"mcp/Controls.lean")),
 ("index-controls",lean(HERE/"index/Controls.lean")),
 ("index-audit",lean(HERE/"index/Audit.lean")),
 ("route-controls",lean(HERE/"routes/Controls.lean")),
 ("route-audit",lean(HERE/"routes/ChangedAudit.lean")),
 ("route-specimens",lean(HERE/"routes/Specimens.lean")),
 ("run-baseline",local_lean("Baseline",True)),
 ("run-compare",local_lean("Compare",True)),
 ("run-audit",lean(R/"AuditRender.lean")),
 ("view-driver",lean(ROOT/"tools/Drivers/View.lean")),
 ("preview-build",lean(HERE/"mcp/Preview.lean")),
 ("preview-protocol",["python3",str(HERE/"mcp/probe.py")]),
]
sources=["tools/Tools/Graph/Index.lean","tools/Tools/View/Flow.lean","tools/Tools/View/FlowLaws.lean","tools/Tools/View/Graph.lean","tools/Tools/View/Run.lean","tools/Tools/Session/Snapshot.lean"]
record={"base":"9389e543ad1325a603732b7802344d79b3b98c61","head_before_commit":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),"threads":3,"checks":[],"source_sha256":{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},"all_passed":False}
for name,cmd in jobs:
    start=time.monotonic()
    out=subprocess.run(cmd,cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=LOG/(name+".log")
    log.write_text(out.stdout)
    record["checks"].append({"name":name,"command":cmd,"exit_code":out.returncode,"seconds":time.monotonic()-start,"finished_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"log_sha256":hashlib.sha256(log.read_bytes()).hexdigest()})
    (LOG/"verification.json").write_text(json.dumps(record,indent=2)+"\n")
    print(name,out.returncode,flush=True)
    if out.returncode:
        print(out.stdout[-6000:])
        raise SystemExit(out.returncode)
record["all_passed"]=True
(LOG/"verification.json").write_text(json.dumps(record,indent=2)+"\n")
