from pathlib import Path
import json,subprocess,os,hashlib,time,shutil
out=Path('/tmp/effect4-duplicate-overwatch-0647')
audit_source=Path(__file__).resolve().with_name('Audit.lean')
if audit_source != (out/'Audit.lean').resolve():
 shutil.copyfile(audit_source,out/'Audit.lean')
m=json.loads((out/'manifest.json').read_text())
env={**os.environ,'LEAN_NUM_THREADS':'3','LEAN_PATH':m['LEAN_PATH']}
cmd=[m['compiler'],'-DwarningAsError=true','Audit.lean']
start=time.monotonic()
p=subprocess.run(cmd,cwd=out,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(out/'Audit.log').write_text(p.stdout)
m['checks'].append({'command':cmd,'cwd':str(out),'exitCode':p.returncode,'seconds':round(time.monotonic()-start,3),'log':'Audit.log'})
(out/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print(p.stdout)
raise SystemExit(p.returncode)
