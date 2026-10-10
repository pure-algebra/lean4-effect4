"""Run finite controls against the owner's stable compiled imports; never build its worktree."""
import datetime, hashlib, json, os, pathlib, re, subprocess, sys, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[2]
owner = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
primary = pathlib.Path('/Users/pooks/Dev/lean4-effect4')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def closure():
    todo=['Effect4.Api','Effect4.Codegen.ClassTable']; seen={}
    if not sys.argv[1:] or 'audit' in sys.argv[1:]: todo.append('Effect4.Laws.Codegen.Definitions')
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
os.environ['LEAN_PATH']=str(packet.parent/'2026-10-10-module-layer-step2b-review/.audit-lib')+':'+str(owner/'.lake/build/lib/lean')+':'+os.environ['LEAN_PATH']
before=snapshot()
commands=[]
checks=[('lean-requirements',['lean','-M6144','-DwarningAsError=true',str(packet/'Requirements.lean')],0),
        ('lean-names-services',['lean','-M6144','-DwarningAsError=true',str(packet/'NamesAndServices.lean')],0),
        ('tsgo-version',[str(primary/'harness/truth/node_modules/.bin/tsgo'),'--version'],0)]
checks += [(name,[str(primary/'harness/truth/node_modules/.bin/tsgo'),'--project',str(packet/(name+'.json'))],expected)
    for name,expected in [('planned-negative',1),('planned-positive',0),('candidate-positive',0),('candidate-negative',1),('service-negative',1)]]
checks += [('bun-version',['bun','--version'],0)]
checks += [(name+'-run',['bun',str(packet/(name+ext))],0)
    for name,ext in [('planned-positive','.ts'),('candidate-positive','.ts'),('name-capture','.mjs')]]
checks.append(('audit',['lean','-M6144','-DwarningAsError=true',str(packet/'Audit.lean')],0))
selected = sys.argv[1:]
if selected: checks = [check for check in checks if check[0] in selected]
for name,argv,expected in checks:
    t=time.monotonic()
    done=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
    record={'name':name,'argv':argv,'expected_exit':expected,'exit':done.returncode,'seconds':round(time.monotonic()-t,3),'output':done.stdout}
    expected_fragments={
      'planned-negative':['TS2375','k4_4','never'],
      'candidate-negative':['TS2379','k4_4','never'],
      'service-negative':['Expected 2 arguments, but got 1.','Expected 2 arguments, but got 0.']}
    record['expected_diagnostics_present']=all(x in done.stdout for x in expected_fragments.get(name,[]))
    commands.append(record)
    print(name, done.returncode, done.stdout[:4500],flush=True)
after=snapshot()
changed=[f for f in before.keys()|after.keys() if before.get(f)!=after.get(f)]
record={'run_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'owner_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=owner,text=True).strip(),
        'review_parent':subprocess.check_output(['git','rev-parse','HEAD'],cwd=review,text=True).strip(),
        'source_modules':len(sources),'changed_inputs':changed,'commands':commands,
        'lean_path':os.environ['LEAN_PATH'],
        'source_differences_from_primary':[str(f.relative_to(owner)) for f in sources.values()
            if (primary/f.relative_to(owner)).exists() and sha(f)!=sha(primary/f.relative_to(owner))],
        'guards':{f.name:f.read_text().count('#guard ') for f in [packet/'Requirements.lean',packet/'NamesAndServices.lean']},
        'limits':['Owner compiled imports were reused, not rebuilt from source',
          'Handwritten TypeScript design projections, not generated modules',
          'Finite value observations only; no universal translation or scheduling theorem']}
(packet/('inputs-before' + (('-' + '-'.join(selected)) if selected else '') + '.json')).write_text(json.dumps(before,indent=2)+'\n')
(packet/('inputs-after' + (('-' + '-'.join(selected)) if selected else '') + '.json')).write_text(json.dumps(after,indent=2)+'\n')
(packet/('checked-results' + (('-' + '-'.join(selected)) if selected else '') + '.json')).write_text(json.dumps(record,indent=2)+'\n')
print('changed inputs', changed)
raise SystemExit(1 if changed or any(c['exit']!=c['expected_exit'] or not c['expected_diagnostics_present'] for c in commands) else 0)
