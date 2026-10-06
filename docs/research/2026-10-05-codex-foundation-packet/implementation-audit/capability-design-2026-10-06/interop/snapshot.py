from pathlib import Path
import subprocess,json,hashlib,sys
root=Path(__file__).parent
m=json.loads((root/'source-manifest.json').read_text()); rev=m['commit']
for p in sys.argv[1:]:
 if any(r['path']==p for r in m['files']): continue
 b=subprocess.check_output(['git','show',rev+':'+p]); out=root/'sources'/p; out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b)
 m['files'].append({'path':p,'commit':rev,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'snapshot':str(out)})
(root/'source-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print(len(m['files']),'frozen source files')
