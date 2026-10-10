"""Run isolated finite controls and a cycle-aware audit of imported draft laws."""
import datetime, hashlib, json, os, pathlib, re, subprocess, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[2]
impl = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
cache = packet / '.audit-lib'
for name in ['ProofGraph', 'Tools/Graph']:
    target = cache / name
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['cp','-c','-R',str(review / '.lake/build/lib/lean' / name),str(target)],check=True)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def git(*args):
    return subprocess.check_output(['git','-C',str(impl),*args],text=True)
def closure():
    todo=[]
    for file in ['Probe.lean','Audit.lean']:
        todo += re.findall(r'^import ([A-Za-z0-9_.]+)',(packet/file).read_text(),re.M)
    found={}
    while todo:
        name=todo.pop()
        if name in found:
            continue
        rel=pathlib.Path(*name.split('.')).with_suffix('.lean')
        root=impl if name.startswith('Effect4.') or name=='Effect4' else review
        source=next((root/base/rel for base in ['src','tools','.'] if (root/base/rel).is_file()),None)
        if source is None:
            continue
        found[name]=(root,source)
        todo += re.findall(r'^(?:public )?import (?:all )?([A-Za-z0-9_.]+)',source.read_text(),re.M)
    return found
sources=closure()
def snapshot():
    result={}
    for name,(root,source) in sources.items():
        result[str(source)]=sha(source)
        library=impl/'.lake/build/lib/lean' if root==impl else cache
        stem=library/pathlib.Path(*name.split('.'))
        for suffix in ['.olean','.olean.private','.olean.server','.ir','.trace']:
            artifact=pathlib.Path(str(stem)+suffix)
            if artifact.exists():
                result[str(artifact)]=sha(artifact)
    return result
os.environ['LEAN_NUM_THREADS']='3'
os.environ['LEAN_PATH']=str(cache)+':'+str(impl/'.lake/build/lib/lean')+':'+os.environ['LEAN_PATH']
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
before=snapshot()
(packet/'inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')
(packet/'draft.patch').write_text(git('diff','--binary'))
(packet/'draft-status.txt').write_text(git('status','--short'))
commands=[]
for file in ['Probe.lean','Audit.lean']:
    command=['lean','--root='+str(packet),'-M6144','-DwarningAsError=true',str(packet/file)]
    t0=time.monotonic()
    completed=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    output=packet/(pathlib.Path(file).stem.lower()+'.out')
    output.write_text(completed.stdout)
    item={'command':command,'exit':completed.returncode,'seconds':round(time.monotonic()-t0,3),
          'source_sha256':sha(packet/file),'output_sha256':sha(output)}
    commands.append(item)
    print(json.dumps(item),flush=True)
    print(completed.stdout,flush=True)
after=snapshot()
(packet/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
changed=[name for name in sorted(before.keys()|after.keys()) if before.get(name)!=after.get(name)]
record={'started':started,'implementation_base':git('rev-parse','HEAD').strip(),
        'review_parent':subprocess.check_output(['git','-C',str(review),'rev-parse','HEAD'],text=True).strip(),
        'source_modules':len(sources),'inputs':len(before),'changed_inputs':changed,
        'lean_version':subprocess.check_output(['lean','--version'],text=True).strip(),
        'lean_path':os.environ['LEAN_PATH'],'working_directory':str(review),'commands':commands,
        'draft_sha256':sha(packet/'draft.patch'),'guards':(packet/'Probe.lean').read_text().count('#guard ')}
(packet/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
raise SystemExit(1 if changed or any(c['exit'] for c in commands) else 0)
