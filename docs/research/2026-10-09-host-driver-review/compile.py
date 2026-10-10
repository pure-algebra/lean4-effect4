from pathlib import Path
import os,subprocess,json,sys
r=Path(__file__).resolve().parent
root=r.parents[2]; overlay=root/'.lake/host-coalgebra-review-overlay'
followup='--followup' in sys.argv
base=r/'d4c869ee' if followup else r
logs=r/('checks-d4c869ee' if followup else 'checks'); logs.mkdir(exist_ok=True)
items=[('host-driver',base/'snapshot/src',base/'snapshot/src/Effect4/Laws/Api/HostDrive.lean',overlay/'Effect4/Laws/Api/HostDrive.olean'),
 ('axiom-command',base/'snapshot/tools',base/'snapshot/tools/ProofGraph/AxiomAudit.lean',overlay/'ProofGraph/AxiomAudit.olean'),
 ('session-battery',None,base/'snapshot/Test/Api/SessionMeaning.lean',None)]
if followup: items=[item for item in items if item[0]!='axiom-command']
results=[]
for name,srcroot,src,out in items:
    cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true']
    if out:
        out.parent.mkdir(parents=True,exist_ok=True)
        for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
            p=out.with_suffix(suffix)
            if p.exists(): p.unlink()
        cmd+=['--root='+str(srcroot),'-o',str(out)]
    cmd.append(str(src)); print('CHECK '+name,flush=True)
    p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(name+'.log')).write_text(p.stdout)
    results.append({'name':name,'command':cmd,'exit_code':p.returncode}); (logs/'build-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('RESULT '+str(p.returncode),flush=True)
    if p.stdout: print(p.stdout,flush=True)
    if p.returncode: sys.exit(p.returncode)
