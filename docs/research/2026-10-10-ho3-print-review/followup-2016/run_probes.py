"""Finite invocation checks against the recorded owner build."""
import datetime, hashlib, json, os, pathlib, re, subprocess, sys, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[3]
owner = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
primary = pathlib.Path('/Users/pooks/Dev/lean4-effect4')
modes = sys.argv[1:] or ['generate', 'runtime']
tsgo = primary/'harness/truth/node_modules/.bin/tsgo'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def closure():
    todo=(['Effect4.Program.Native', 'Effect4.Codegen.PrintTyped'] if modes == ['typed'] else ['Effect4.Api', 'Effect4.Codegen.PrintTyped']); seen={}
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
os.environ['LEAN_PATH']=str(owner/'.lake/build/lib/lean')+':'+os.environ['LEAN_PATH']
before=snapshot(); commands=[]
def run(name, argv, expected=0, fragments=()):
    t=time.monotonic()
    done=subprocess.run([str(a) for a in argv], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=180)
    commands.append({'name':name,'argv':[str(a) for a in argv], 'expected_exit':expected,
        'exit':done.returncode,'seconds':round(time.monotonic()-t,3),'output':done.stdout,
        'expected_diagnostics_present':all(f in done.stdout for f in fragments)})
    print(name, done.returncode, done.stdout[:6500], flush=True)
    return done
run('tsgo-version',[tsgo,'--version'],fragments=['7.0.0-dev.20260629.1'])
if 'generate' in modes:
    generated=run('generate',['lean','-M6144','-DwarningAsError=true',packet/'Generated.lean'])
    if generated.returncode==0:
        rows=[json.loads(line) for line in generated.stdout.splitlines() if line.startswith('{')]
        assert len(rows)==10, len(rows)
        (packet/'generated-output.json').write_text(json.dumps(rows,indent=2)+'\n')
        prefix='import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "'+str(primary/'harness/truth/node_modules/effect/dist/index.js')+'";\n'
        for row in rows:
            name=row['name']
            (packet/(name+'.generated.ts')).write_text(row['source'])
            (packet/(name+'.ts')).write_text(prefix+row['source'])
        runtime=prefix+''.join('import { main as p'+str(i)+' } from "./'+r['name']+'.ts";\n' for i,r in enumerate(rows))
        runtime+='const actual = await Promise.all(['+', '.join('Effect.runPromise(p'+str(i)+')' for i in range(len(rows)))+']);\n'
        runtime+='const expected = '+json.dumps([r['expected'] for r in rows])+';\n'
        runtime+='if (JSON.stringify(actual) !== JSON.stringify(expected)) throw new Error(JSON.stringify({ actual, expected }));\nconsole.log(JSON.stringify(actual));\n'
        (packet/'positive-runtime.ts').write_text(runtime)
        config={'extends':str(primary/'harness/truth/tsconfig.json'),
            'compilerOptions':{'typeRoots':[str(primary/'harness/truth/node_modules/@types')]},
            'files':[str(packet/'positive-runtime.ts')],'include':[],'exclude':[]}
        (packet/'positive-runtime.json').write_text(json.dumps(config,indent=2)+'\n')
if 'runtime' in modes and (packet/'positive-runtime.ts').exists():
    run('runtime-typecheck',[tsgo,'--project',packet/'positive-runtime.json'])
    run('bun-version',['bun','--version'])
    run('positive-runtime',['bun',packet/'positive-runtime.ts'],fragments=['[5,11,5,11,5,3,29,11,17,37]'])
if 'typed' in modes:
    # The owner's erasure source is newer than its compiled file. Rebuild only this
    # module into the review overlay; never write an artifact in the owner worktree.
    overlay=packet/'.verified-lib'
    out=overlay/'Effect4/Codegen/EraseTypes.olean'
    out.parent.mkdir(parents=True,exist_ok=True)
    # Lean resolves a package from one search root. Point every unchanged module
    # back to the owner package and keep only EraseTypes as a real local artifact.
    source_lib=owner/'.lake/build/lib/lean'
    for entry in source_lib.glob('Effect4.*'):
        dest=overlay/entry.name
        if not dest.exists(): dest.symlink_to(entry)
    for entry in (source_lib/'Effect4').iterdir():
        if entry.name == 'Codegen': continue
        dest=overlay/'Effect4'/entry.name
        if not dest.exists(): dest.symlink_to(entry, target_is_directory=entry.is_dir())
    for entry in (source_lib/'Effect4/Codegen').iterdir():
        if entry.name.startswith('EraseTypes.'): continue
        dest=overlay/'Effect4/Codegen'/entry.name
        if not dest.exists(): dest.symlink_to(entry, target_is_directory=entry.is_dir())
    local_root=packet/'.source'
    local_source=local_root/'Effect4/Codegen/EraseTypes.lean'
    local_source.parent.mkdir(parents=True,exist_ok=True)
    local_source.write_bytes((owner/'src/Effect4/Codegen/EraseTypes.lean').read_bytes())
    assert sha(local_source) == before[str(owner/'src/Effect4/Codegen/EraseTypes.lean')]
    built=run('compile-erasure',['lean','-M6144','-DwarningAsError=true','-R',local_root,
        '-o',out,local_source])
    if built.returncode != 0: raise SystemExit('Review-only erasure rebuild failed')
    os.environ['LEAN_PATH']=str(overlay)+':'+os.environ['LEAN_PATH']
    run('typed-sites',['lean','-M6144','-DwarningAsError=true',packet/'TypedSites.lean'])
after=snapshot()
changed=[f for f in before.keys()|after.keys() if before.get(f)!=after.get(f)]
record={'run_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'owner_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=owner,text=True).strip(),
    'review_parent':subprocess.check_output(['git','rev-parse','HEAD'],cwd=review,text=True).strip(),
    'source_modules':len(sources),'verified_overlay':{str(f):sha(f) for f in (packet/'.verified-lib').rglob('*') if f.is_file() and not f.is_symlink()},'changed_inputs':changed,'commands':commands,'lean_path':os.environ['LEAN_PATH'],
    'limits':['Owner compiled imports reused; EraseTypes alone rebuilt from current source for typed mode',
      'Generated declarations unchanged; explicit Effect imports prepended',
      'Finite values and reconstruction only; no universal target or scheduling theorem']}
suffix='-'+('-'.join(modes))
(packet/('inputs-before'+suffix+'.json')).write_text(json.dumps(before,indent=2)+'\n')
(packet/('inputs-after'+suffix+'.json')).write_text(json.dumps(after,indent=2)+'\n')
(packet/('checked-results'+suffix+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print('changed inputs',changed,flush=True)
raise SystemExit(1 if changed or any(c['exit']!=c['expected_exit'] or not c['expected_diagnostics_present'] for c in commands) else 0)
