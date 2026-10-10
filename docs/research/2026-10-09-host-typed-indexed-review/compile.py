from pathlib import Path
import os, subprocess, json
r=Path(__file__).resolve().parent; root=r.parents[2]
overlay=root/'.lake/host-coalgebra-review-overlay'
logs=r/'checks'; logs.mkdir(exist_ok=True)
# One new module at a time; all unchanged dependencies come from the reviewed overlay.
items=[('sat',r/'snapshot/effects',r/'snapshot/effects/Effects/Coalgebra/Sat.lean',overlay/'Effects/Coalgebra/Sat.olean'),
('indexed',r/'snapshot/effects',r/'snapshot/effects/Effects/Coalgebra/Indexed.lean',overlay/'Effects/Coalgebra/Indexed.olean'),
('coalgebra-root',r/'snapshot/effects',r/'snapshot/effects/Effects/Coalgebra.lean',overlay/'Effects/Coalgebra.olean'),
('package-battery',r/'snapshot/effects',r/'snapshot/effects/EffectsTest/Coalgebra/CoalgebraContract.lean',overlay/'EffectsTest/Coalgebra/CoalgebraContract.olean'),
('host-driver',r/'snapshot/effect4/src',r/'snapshot/effect4/src/Effect4/Laws/Api/HostDrive.lean',overlay/'Effect4/Laws/Api/HostDrive.olean'),
('session-battery',None,r/'snapshot/effect4/Test/Api/SessionMeaning.lean',None)]
results=[]
for name,srcroot,src,out in items:
    cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true']
    if name in ['sat','indexed','coalgebra-root','package-battery']:
        cmd+=['-DautoImplicit=false','-DrelaxedAutoImplicit=false']
    if out:
        out.parent.mkdir(parents=True,exist_ok=True)
        for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
            f=out.with_suffix(suffix)
            if f.exists(): f.unlink()
        cmd+=['--root='+str(srcroot),'-o',str(out)]
    cmd.append(str(src))
    print('CHECK '+name,flush=True)
    p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(name+'.log')).write_text(p.stdout)
    results.append({'name':name,'command':cmd,'exit_code':p.returncode})
    (logs/'build-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('RESULT '+str(p.returncode),flush=True)
    if p.stdout: print(p.stdout,flush=True)
    if p.returncode:raise SystemExit(p.returncode)
