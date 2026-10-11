from pathlib import Path
import os, subprocess, json, sys
r=Path(__file__).resolve().parent; root=r.parents[2]
overlay=root/'.lake/host-coalgebra-review-overlay'
logs=r/'checks-followup'; logs.mkdir(exist_ok=True)
# One new module at a time; all unchanged dependencies come from the reviewed overlay.
items=[('run-completeness',r/'followup/effects',r/'followup/effects/Effects/Coalgebra/Run.lean',overlay/'Effects/Coalgebra/Run.olean'),
('coalgebra-root',r/'followup/effects',r/'followup/effects/Effects/Coalgebra.lean',overlay/'Effects/Coalgebra.olean'),
('package-battery',r/'followup/effects',r/'followup/effects/EffectsTest/Coalgebra/CoalgebraContract.lean',overlay/'EffectsTest/Coalgebra/CoalgebraContract.olean'),
('host-driver',r/'followup/effect4/src',r/'followup/effect4/src/Effect4/Laws/Api/HostDrive.lean',overlay/'Effect4/Laws/Api/HostDrive.olean')]

results=json.loads((logs/'build-results.json').read_text()) if (logs/'build-results.json').exists() else []
for name,srcroot,src,out in items:
    if sys.argv[1:] and name not in sys.argv[1:]: continue
    results=[item for item in results if item['name'] != name]
    cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true']
    if name in ['run-completeness','coalgebra-root','package-battery']:
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
