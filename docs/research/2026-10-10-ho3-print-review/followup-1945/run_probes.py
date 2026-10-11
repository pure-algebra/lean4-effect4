"""Generate finite target controls from the owner's compiled HO-3a imports."""
import datetime, hashlib, json, os, pathlib, re, subprocess, sys, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[3]
owner = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
primary = pathlib.Path('/Users/pooks/Dev/lean4-effect4')
selected = sys.argv[1:]
tsgo = primary/'harness/truth/node_modules/.bin/tsgo'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def closure():
    todo=['Effect4.Api', 'Effect4.Laws.Api.ModuleReadable']; seen={}
    while todo:
        name=todo.pop()
        if name in seen: continue
        source=owner/'src'/pathlib.Path(*name.split('.')).with_suffix('.lean')
        if not source.exists(): continue
        seen[name]=source
        todo += re.findall(r'^(?:public )?import (?:all )?([A-Za-z0-9_.]+)', source.read_text(), re.M)
    return seen
sources=closure()
def snapshot():
    out={}
    for name,source in sources.items():
        out[str(source)]=sha(source)
        stem=owner/'.lake/build/lib/lean'/pathlib.Path(*name.split('.'))
        for suffix in ['.olean','.olean.private','.olean.server','.ir','.trace']:
            f=pathlib.Path(str(stem)+suffix)
            if f.exists(): out[str(f)]=sha(f)
    for f in [primary/'harness/truth/node_modules/effect/package.json',
              primary/'harness/truth/node_modules/@typescript/native-preview/package.json',
              primary/'harness/truth/tsconfig.json']:
        out[str(f)]=sha(f)
    return out
os.environ['LEAN_NUM_THREADS']='3'
os.environ['LEAN_PATH']=str(packet.parent.parent/'2026-10-10-module-layer-step2b-review/.audit-lib')+':'+str(owner/'.lake/build/lib/lean')+':'+os.environ['LEAN_PATH']
before=snapshot()
commands=[]
def run(name, argv, expected=0, fragments=()):
    t=time.monotonic()
    done=subprocess.run([str(a) for a in argv], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=180)
    record={'name':name,'argv':[str(a) for a in argv], 'expected_exit':expected,
        'exit':done.returncode,'seconds':round(time.monotonic()-t,3),'output':done.stdout,
        'expected_diagnostics_present':all(f in done.stdout for f in fragments)}
    commands.append(record)
    print(name, done.returncode, done.stdout[:5000], flush=True)
    return done
run('tsgo-version',[tsgo,'--version'],fragments=['7.0.0-dev.20260629.1'])
if not selected or 'inventory' in selected:
    run('inventory',['lean','-M6144','-DwarningAsError=true',packet/'AnnotationFormation.lean'])
if not selected or 'generate' in selected:
    generated=run('generate',['lean','-M6144','-DwarningAsError=true',packet/'Generated.lean'])
    if generated.returncode==0:
        rows=[json.loads(line) for line in generated.stdout.splitlines() if line.startswith('{')]
        assert len(rows)==12, len(rows)
        (packet/'generated-output.json').write_text(json.dumps(rows,indent=2)+'\n')
        prefix='import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "'+str(primary/'harness/truth/node_modules/effect/dist/index.js')+'";\n'
        fixture='const Widget = { run: (n: number) => Effect.succeed(n + 1) };\nconst Token = 7;\nconst readWidget = (_n: number, token: number) => Effect.succeed(token);\n'
        for row in rows:
            name=row['name']
            (packet/(name+'.generated.ts')).write_text(row['source'])
            (packet/(name+'.ts')).write_text(prefix+fixture+row['source'])
            config={'extends':str(primary/'harness/truth/tsconfig.json'),
                'compilerOptions':{'typeRoots':[str(primary/'harness/truth/node_modules/@types')]},
                'files':[str(packet/(name+'.ts'))],'include':[],'exclude':[]}
            (packet/(name+'.json')).write_text(json.dumps(config,indent=2)+'\n')
if not selected or 'generate' in selected or 'targets' in selected:
    rows=json.loads((packet/'generated-output.json').read_text())
    expected={
        'payload-negative':['TS7009', 'construct signature'],
        'qualified-negative':['TS2339', 'run'],
        'trailing-negative':['TS2345'],
        'service-method-negative':['Expected 2 arguments, but got 1.'],
        'service-init-negative':['Expected 2 arguments, but got 0.'],
        'parameter-class-negative':['TS2304', 'OnlyParam']}
    for row in rows:
        name=row['name']
        run(name,[tsgo,'--project',packet/(name+'.json')],1 if name in expected else 0,expected.get(name,()))
if not selected or 'runtime' in selected:
    run('runtime-typecheck',[tsgo,'--project',packet/'positive-runtime.json'])
    run('bun-version',['bun','--version'])
    run('positive-runtime',['bun',packet/'positive-runtime.ts'],fragments=['[7,7,8,7,7,1]'])
if not selected or 'audit' in selected:
    run('audit',['lean','-M6144','-DwarningAsError=true',packet/'Audit.lean'])
after=snapshot()
changed=[f for f in before.keys()|after.keys() if before.get(f)!=after.get(f)]
record={'run_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'owner_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=owner,text=True).strip(),
        'review_parent':subprocess.check_output(['git','rev-parse','HEAD'],cwd=review,text=True).strip(),
        'source_modules':len(sources),'changed_inputs':changed,'commands':commands,
        'lean_path':os.environ['LEAN_PATH'],
        'limits':['Owner compiled imports were reused, not rebuilt from source',
          'Generated declarations remain unchanged; explicit fixture imports and globals are prepended',
          'Finite target type checks only; no universal translation or scheduling theorem']}
suffix='-'+('-'.join(selected)) if selected else ''
(packet/('inputs-before'+suffix+'.json')).write_text(json.dumps(before,indent=2)+'\n')
(packet/('inputs-after'+suffix+'.json')).write_text(json.dumps(after,indent=2)+'\n')
(packet/('checked-results'+suffix+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print('changed inputs', changed, flush=True)
raise SystemExit(1 if changed or any(c['exit']!=c['expected_exit'] or not c['expected_diagnostics_present'] for c in commands) else 0)
