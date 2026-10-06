from pathlib import Path
import subprocess,json,time,hashlib,sys
out=Path(__file__).parent
exe='/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/@typescript/native-preview/bin/tsgo'
results=[]
for variant in sys.argv[1:]:
 cwd=out/'inputs'/variant
 cmd=['node',exe,'--pretty','false','--noEmit','-p',str(cwd/'tsconfig.json')]
 start=time.monotonic();p=subprocess.run(cmd,cwd=cwd,text=True,capture_output=True,timeout=45)
 log=p.stdout+p.stderr
 (out/'outputs'/f'{variant}.log').write_text(log)
 row={'variant':variant,'command':cmd,'cwd':str(cwd),'exit':p.returncode,'seconds':round(time.monotonic()-start,3),'log_sha256':hashlib.sha256(log.encode()).hexdigest(),'diagnostic_count':log.count('error TS')}
 results.append(row)
 print(variant,p.returncode,row['diagnostic_count']);print(log[:7000])
 p=out/'outputs'/'runs.json';old=json.loads(p.read_text()) if p.exists() else []
 old.append(row);p.write_text(json.dumps(old,indent=2)+'\n')
