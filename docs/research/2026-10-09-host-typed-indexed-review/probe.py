from pathlib import Path
import os, subprocess, json, sys
r=Path(__file__).resolve().parent; root=r.parents[2]
overlay=root/'.lake/host-coalgebra-review-overlay'
logs=r/'checks-followup'; logs.mkdir(exist_ok=True)
results=json.loads((logs/'probe-results.json').read_text()) if (logs/'probe-results.json').exists() else []
for module in (sys.argv[1:] or ['TypedLayerControls','IndexedControls','SessionControls','Audit']):
    results=[item for item in results if item['name'] != module]
    cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true',str(r/(module+'.lean'))]
    print('CHECK '+module,flush=True)
    p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(module+'.log')).write_text(p.stdout)
    results.append({'name':module,'command':cmd,'exit_code':p.returncode})
    (logs/'probe-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('RESULT '+str(p.returncode),flush=True)
    if p.stdout: print(p.stdout,flush=True)
    if p.returncode: raise SystemExit(p.returncode)
