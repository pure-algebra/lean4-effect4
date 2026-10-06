from pathlib import Path
import json,subprocess,hashlib,time,re
out=Path(__file__).parent
exe='/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/@typescript/native-preview/bin/tsgo'
rows=[]
for n in ['baseline','revised']:
 d=out/'inputs'/('emit-'+n);d.mkdir(exist_ok=True)
 source=(out/'inputs'/n/'prelude-atoms.gen.ts').read_text()
 wanted=[line for line in source.splitlines() if line.startswith(('type Wide<','export const pair =','export const tuple ='))]
 (d/'helpers.ts').write_text('\n'.join(wanted)+'\n')
 (d/'tsconfig.json').write_text(json.dumps({'compilerOptions':{'target':'ES2022','module':'ESNext','strict':True,'types':[],'outDir':'../../outputs/emit-'+n},'files':['helpers.ts']},indent=2)+'\n')
 cmd=['node',exe,'--pretty','false','-p',str(d/'tsconfig.json')]
 p=subprocess.run(cmd,cwd=d,capture_output=True,text=True,timeout=30)
 (out/'outputs'/('emit-'+n+'.log')).write_text(p.stdout+p.stderr)
 js=out/'outputs'/('emit-'+n)/'helpers.js'
 rows.append({'variant':n,'command':cmd,'cwd':str(d),'exit':p.returncode,'input_sha256':hashlib.sha256((d/'helpers.ts').read_bytes()).hexdigest(),'js_sha256':hashlib.sha256(js.read_bytes()).hexdigest() if js.exists() else None})
 print(n,p.returncode,p.stdout+p.stderr)
a=out/'outputs/emit-baseline/helpers.js';b=out/'outputs/emit-revised/helpers.js';identical=a.read_bytes()==b.read_bytes();assert identical
(out/'outputs/emit-comparison.json').write_text(json.dumps({'runs':rows,'byte_identical':identical,'bytes':a.stat().st_size,'observation':'Emitted helper JavaScript only. No runtime run or semantic theorem.'},indent=2)+'\n')
print('helper JavaScript byte-identical',a.stat().st_size)
print(a.read_text())
