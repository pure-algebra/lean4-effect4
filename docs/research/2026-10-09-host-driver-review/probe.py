from pathlib import Path
import os, subprocess, json, sys
r=Path(__file__).resolve().parent
root=r.parents[2]; overlay=root/'.lake/host-coalgebra-review-overlay'
followup='--followup' in sys.argv or '--entries' in sys.argv
logs=r/('checks-d4c869ee' if followup else 'checks'); logs.mkdir(exist_ok=True)
items=[('driver-controls','DriverControls',False,0),
       ('driver-audit','DriverAudit',False,0),
       ('hidden-fixture','AuditHidden',True,0),
       ('clean-fixture','AuditClean',True,0),
       ('audit-positive','AuditPositive',False,0),
       ('audit-restricted','AuditRestricted',False,1),
       ('audit-full','AuditFull',False,1)]
if followup: items=[('adapter-controls','HostAdapterControls',False,0),('driver-audit','DriverAudit',False,0),('public-run','PublicRunControls',False,1),('public-laws','PublicLawsControls',False,1)]
if '--entries' in sys.argv: items=[item for item in items if item[0].startswith('public-')]
results=[]
for name,module,compile,expected in items:
    cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true']
    if compile:
        out=overlay/(module+'.olean')
        for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
            f=out.with_suffix(suffix)
            if f.exists(): f.unlink()
        cmd+=['--root='+str(r),'-o',str(out)]
    cmd.append(str(r/(module+'.lean')))
    print('CHECK '+name,flush=True)
    p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(name+'.log')).write_text(p.stdout)
    results.append({'name':name,'command':cmd,'expected_exit':expected,'exit_code':p.returncode})
    (logs/('entry-results.json' if '--entries' in sys.argv else 'probe-results.json')).write_text(json.dumps(results,indent=2)+'\n')
    print('RESULT '+str(p.returncode),flush=True)
    if p.stdout: print(p.stdout,flush=True)
    if expected is not None and p.returncode!=expected: raise SystemExit(p.returncode or 2)
    if name=='audit-restricted' and 'cannot import non-`module` ProofGraph.AxiomAudit from `module`' not in p.stdout: raise SystemExit(3)
    if name=='public-run' and ('Unknown constant `Effect4.Run.Reactor.guardRows`' not in p.stdout or 'Unknown constant `Effect4.Run.rowPosition`' not in p.stdout): raise SystemExit(5)
    if name=='public-laws' and 'Unknown constant `Effect4.Run.Reactor.ofHost`' not in p.stdout: raise SystemExit(6)
    if name=='audit-full' and ('hiddenChoice' not in p.stdout or 'Classical.choice' not in p.stdout or '#axiom_audit:' not in p.stdout): raise SystemExit(4)
