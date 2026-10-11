from pathlib import Path
import json,os,subprocess
r=Path(__file__).resolve().parent;root=r.parents[2];logs=r/'checks'
results=[]
for name,run in [('Controls',True),('Axioms',False)]:
 cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(root/'.lake/service-repair-overwatch'),'-DwarningAsError=true']+(['--run'] if run else [])+[str(r/(name+'.lean'))]
 print('CHECK '+name,flush=True)
 p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (logs/(name+'.log')).write_text(p.stdout)
 results.append({'name':name,'command':cmd,'exit_code':p.returncode})
 (logs/'lean-results.json').write_text(json.dumps(results,indent=2)+'\n')
 print(p.stdout,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
