from pathlib import Path
import subprocess,time,json,hashlib
out=Path(__file__).resolve().parent
assert all(r['exit_code']==0 for r in json.loads((out/'lean-results.json').read_text()))
repo=Path('/Users/pooks/Dev/lean4-effect4')
deps=repo/'ts/eff/node_modules'
node='/Users/pooks/.local/share/mise/shims/node'
options=dict(strict=True,target='ES2022',module='ESNext',moduleResolution='bundler',lib=['ESNext','DOM'],
    noEmit=True,exactOptionalPropertyTypes=True,noUncheckedIndexedAccess=True,skipLibCheck=True,types=[])
for name,files in [('green',['inference.ts']),('red',['duplicate-red.ts'])]:
    (out/f'tsconfig-{name}.json').write_text(json.dumps(dict(compilerOptions=options,files=files),indent=2))
pins=dict(effect=json.loads((deps/'effect/package.json').read_text())['version'],
    typescript=json.loads((deps/'typescript/package.json').read_text())['version'],
    node=subprocess.check_output([node,'--version'],text=True).strip(),sources={})
for f in ['Schema.ts','SchemaAST.ts','SchemaParser.ts','SchemaRepresentation.ts','internal/schema/fromRepresentation.ts']:
    vendor=(repo/'vendor/effect-4.0.0-rc.112/src'/f).read_bytes()
    installed=(deps/'effect/src'/f).read_bytes()
    assert vendor==installed
    pins['sources'][f]=hashlib.sha256(vendor).hexdigest()
(out/'host-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
results=[]
for name,cmd,expected in [
    ('runtime',[node,'--max-old-space-size=1024',str(out/'runtime.mjs')],0),
    ('inference-green',[node,'--max-old-space-size=1024',str(deps/'typescript/lib/tsc.js'),'-p',str(out/'tsconfig-green.json'),'--pretty','false'],0),
    ('duplicate-red',[node,'--max-old-space-size=1024',str(deps/'typescript/lib/tsc.js'),'-p',str(out/'tsconfig-red.json'),'--pretty','false'],2)]:
    start=time.monotonic()
    p=subprocess.run(cmd,cwd=out,text=True,capture_output=True,timeout=30)
    log=p.stdout+p.stderr
    (out/f'{name}.log').write_text(log)
    results.append(dict(name=name,command=cmd,cwd=str(out),exit_code=p.returncode,expected_exit=expected,seconds=round(time.monotonic()-start,3)))
    (out/'host-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(name,p.returncode,log,flush=True)
    assert p.returncode==expected
    if name=='duplicate-red':assert 'error TS1117' in log
