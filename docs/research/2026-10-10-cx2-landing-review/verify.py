#!/usr/bin/env python3
"""Check the pinned CX2 proof slice with serialized, narrow Lean commands."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib, json, os, shlex, subprocess
packet=Path(__file__).resolve().parent
repo=packet.parents[2]
reviewed="9e818b39596971d62b89299ca9ccc4e96ad8ea07"
modules=(packet/"modules.txt").read_text().splitlines()
env=dict(os.environ,LEAN_NUM_THREADS="3")
report={"reviewed_commit":reviewed,"previous_commit":"f00008eeaef00b67fe93cfd0327754c9f42694ee","checks":{}}
def checked(name,args):
    started=datetime.now(timezone.utc).isoformat()
    r=subprocess.run(args,cwd=repo,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log="$ "+shlex.join(args)+"\n"+r.stdout+"\nExit: "+str(r.returncode)+"\n"
    (packet/(name+".log")).write_text(log)
    report["checks"][name]={"command":args,"started_utc":started,"exit":r.returncode,"log_sha256":hashlib.sha256(log.encode()).hexdigest()}
    (packet/"verification.json").write_text(json.dumps(report,indent=2)+"\n")
    print(name+": "+str(r.returncode),flush=True)
    if r.returncode:
        print(r.stdout,flush=True)
        raise SystemExit(r.returncode)
checked("source-diff",["git","diff","--exit-code",reviewed,"--","src","Test","tools","lakefile.toml","lake-manifest.json"])
checked("build",["lake","build",*modules,"Effect4.Laws.Program.Typed.Commands.Clauses.All","ProofGraph.AxiomAudit","ProofGraph.Plan"])
checked("audit",["lake","env","lean","-DwarningAsError=true",str(packet/"Audit.lean")])
report["source_sha256"]={"src/"+m.replace(".","/")+".lean":hashlib.sha256((repo/("src/"+m.replace(".","/")+".lean")).read_bytes()).hexdigest() for m in modules}
report["probe_sha256"]=hashlib.sha256((packet/"Audit.lean").read_bytes()).hexdigest()
report["all_recorded_passed"]=True
(packet/"verification.json").write_text(json.dumps(report,indent=2)+"\n")
