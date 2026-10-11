from pathlib import Path
import json,os,subprocess,sys
r=Path(__file__).resolve().parent
root=r.parents[2]
overlay=root/'.lake/host-coalgebra-review-overlay'
logs=r/'checks'
logs.mkdir(exist_ok=True)
items=[
('row-protocol',r/'snapshot/src/Effect4/Laws/Program/RowProtocol.lean',r/'snapshot/src',overlay/'Effect4/Laws/Program/RowProtocol.olean'),
('typed-replies',r/'snapshot/Test/Api/TypedReplies.lean',r/'snapshot/Test/Api',overlay/'TypedReplies.olean'),
('row-controls',r/'RowControls.lean',None,None),
('row-axioms',r/'RowAxioms.lean',None,None),
]
results=json.loads((logs/'results.json').read_text())[:2] if len(sys.argv)>1 else []
if len(sys.argv)>1: items=items[2:]
for name,source,srcroot,out in items:
    cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true']
    if out:
        out.parent.mkdir(parents=True,exist_ok=True)
        for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
            old=out.with_suffix(suffix)
            if old.exists(): old.unlink()
        cmd+=['--root='+str(srcroot),'-o',str(out)]
    cmd.append(str(source))
    print('CHECK '+name,flush=True)
    run=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(name+'.log')).write_text(run.stdout)
    results.append({'name':name,'command':cmd,'exit_code':run.returncode})
    (logs/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('RESULT '+str(run.returncode),flush=True)
    if run.stdout: print(run.stdout,flush=True)
    if run.returncode: sys.exit(run.returncode)
