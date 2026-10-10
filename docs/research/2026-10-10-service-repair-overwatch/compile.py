from pathlib import Path
import hashlib,json,os,subprocess
r=Path(__file__).resolve().parent;root=r.parents[2]
overlay=root/'.lake/service-repair-overwatch';logs=r/'checks';logs.mkdir(exist_ok=True)
modules=[('src','Effect4.Codegen.Print'),('src','Effect4.Codegen.Read'),('src','Effect4.Library.Semaphore.Defs'),('src','Effect4.Laws.Codegen.Services'),('src','Effect4.Laws.Codegen.Module'),('','Test.Codegen.ServicesPrint')]
results=[]
for prefix,name in modules:
 source=r/'snapshot'/prefix/Path(*name.split('.')).with_suffix('.lean')
 out=overlay/Path(*name.split('.')).with_suffix('.olean')
 for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir','.ir.sig']:out.with_suffix(suffix).unlink(missing_ok=True)
 cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true','--root='+str(r/'snapshot'/prefix),'-o',str(out),str(source)]
 print('CHECK '+name,flush=True)
 p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (logs/(name+'.log')).write_text(p.stdout)
 results.append({'module':name,'command':cmd,'exit_code':p.returncode,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()})
 (logs/'compile-results.json').write_text(json.dumps(results,indent=2)+'\n')
 print('RESULT '+str(p.returncode),flush=True)
 if p.stdout:print(p.stdout,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
