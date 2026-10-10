"""Compile a proof-only overlay and audit its round-trip consumers."""
import datetime, hashlib, json, os, pathlib, subprocess, time
p=pathlib.Path(__file__).resolve().parent
review=p.parents[2]
impl=pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
build=p/'candidate/.build'
build.mkdir(parents=True,exist_ok=True)
# Lean selects search roots by namespace, so the overlay needs every imported Effect4 artifact.
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
# Reuse the explicitly recorded transitive input set, not a mutable glob of the checkout.
inputs=list(json.loads((p/'inputs-before.json').read_text()))
for name in list(inputs):
    if name.endswith('.ir') and pathlib.Path(name+'.sig').is_file():
        inputs.append(name+'.sig')
for name in inputs:
    source=pathlib.Path(name)
    library=impl/'.lake/build/lib/lean'
    if source.is_relative_to(library):
        target=build/source.relative_to(library)
        target.parent.mkdir(parents=True,exist_ok=True)
        subprocess.run(['cp','-c',str(source),str(target)],check=True)
for rel in ['candidate/src/Effect4/Laws/Codegen/Module.lean',
            'candidate/src/Effect4/Laws/Api/ModuleReadable.lean',
            'OwnerDefinitionsPrint.lean','CandidateDefinitionsPrint.lean','Probe.lean','Audit.lean','Diagnostic.lean']:
    inputs.append(str(p/rel))
def snapshot(): return {name:sha(pathlib.Path(name)) for name in inputs}
os.environ['LEAN_NUM_THREADS']='3'
os.environ['LEAN_PATH']=str(build)+':'+str(p/'.audit-lib')+':'+str(impl/'.lake/build/lib/lean')+':'+os.environ['LEAN_PATH']
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
before=snapshot()
(p/'candidate-inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')
checks=[]
def check(command,label,expected=0):
    start=time.monotonic()
    r=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    output=p/(label+'.out')
    output.write_text(r.stdout)
    item={'command':command,'exit':r.returncode,'expected_exit':expected,
          'seconds':round(time.monotonic()-start,3),'output_sha256':sha(output)}
    checks.append(item)
    print(json.dumps(item),flush=True)
    print(r.stdout,flush=True)
    return r.returncode==expected
common=['lean','-M6144','-DwarningAsError=true']
check(common+[str(p/'Diagnostic.lean')],'diagnostic')
check(common+[str(p/'OwnerDefinitionsPrint.lean')],'owner-fixture',1)
ok=True
for name in ['Effect4.Laws.Codegen.Module','Effect4.Laws.Api.ModuleReadable']:
    relative=pathlib.Path(*name.split('.'))
    source=p/'candidate/src'/relative.with_suffix('.lean')
    target=build/relative.with_suffix('.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    ok=check(common+['--root='+str(p/'candidate/src'),'-o',str(target),str(source)],
             'candidate-'+name.rsplit('.',1)[1]) and ok
    if not ok: break
if ok:
    check(common+[str(p/'Audit.lean')],'candidate-audit')
    check(common+[str(p/'Probe.lean')],'candidate-probe')
    check(common+[str(p/'CandidateDefinitionsPrint.lean')],'candidate-fixture')
after=snapshot()
(p/'candidate-inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
changed=[n for n in before if before[n]!=after[n]]
record={'started':started,'checks':checks,'inputs':len(before),'changed_inputs':changed,
        'implementation_base':subprocess.check_output(['git','-C',str(impl),'rev-parse','HEAD'],text=True).strip(),
        'lean_path':os.environ['LEAN_PATH'],
        'candidate_artifacts':{str(f.relative_to(p)):sha(f) for f in build.rglob('*.olean')}}
(p/'candidate-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['candidate_artifacts','lean_path']},indent=2),flush=True)
raise SystemExit(1 if changed or any(c['exit']!=c['expected_exit'] for c in checks) else 0)
