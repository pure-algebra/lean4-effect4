from pathlib import Path
import hashlib,json,os,subprocess
r=Path(__file__).resolve().parent;root=r.parents[2]
standalone=root/'.lake/service-repair-source-check';standalone.mkdir(exist_ok=True)
overlay=root/'.lake/service-repair-overwatch'
source=r/'snapshot/src/Effect4/Laws/Program/TyView.lean'
cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','review',str(overlay),'-DwarningAsError=true','--root='+str(r/'snapshot/src'),'-o',str(standalone/'TyView.olean'),str(source)]
p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(r/'checks/dependency-source.log').write_text(p.stdout)
assert p.returncode==0,p.stdout
replacements=[]
for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir','.ir.sig']:
 src=standalone/('TyView'+suffix);dst=overlay/'Effect4/Laws/Program'/('TyView'+suffix)
 if src.exists():
  subprocess.run(['cp','-c',str(src),str(dst)],check=True)
  replacements.append({'artifact':str(dst.relative_to(root)),'sha256':hashlib.sha256(dst.read_bytes()).hexdigest()})
 else:dst.unlink(missing_ok=True)
(r/'checks/dependency-source.json').write_text(json.dumps({'command':cmd,'exit_code':p.returncode,'scope':'Committed TyView source compiled and installed over the builder artifact before the final controls and axiom audit.','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'replacements':replacements},indent=2)+'\n')
print('PASS: committed TyView compiled and replaced the captured dependency')
