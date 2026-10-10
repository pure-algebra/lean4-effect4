"""Rebuild the new proof sources, then audit the affected compiled proof graph."""
import datetime, hashlib, json, os, pathlib, re, subprocess, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[3]
owner = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
lib = owner/'.lake/build/lib/lean'
overlay = packet/'.verified-lib'
local = packet/'.source'
modules = ['Effect4.Laws.Codegen.PrintReadable', 'Effect4.Laws.Codegen.PrintTyped']
audited = modules + ['Effect4.Laws.Codegen.Read', 'Effect4.Laws.Codegen.ReadLeaf',
    'Effect4.Laws.Codegen.ReadPrint', 'Effect4.Laws.Codegen.Definitions',
    'Effect4.Laws.Codegen.Module', 'Effect4.Laws.Api.ModuleReadable']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def source(name):
    f=pathlib.Path(*name.split('.')).with_suffix('.lean')
    for folder in ['src','tools']:
        p=owner/folder/f
        if p.exists(): return p
    return None
sources={}; todo=audited+['ProofGraph.AxiomAudit','ProofGraph.Plan']
while todo:
    name=todo.pop()
    if name in sources: continue
    p=source(name)
    if p is None: continue
    sources[name]=p
    todo += re.findall(r'^(?:public )?import (?:all )?([A-Za-z0-9_.]+)',p.read_text(),re.M)
def snapshot():
    rows={}
    for name,p in sources.items():
        rows[str(p)]=sha(p)
        stem=lib/pathlib.Path(*name.split('.'))
        for suffix in ['.olean','.olean.private','.ir','.trace']:
            f=pathlib.Path(str(stem)+suffix)
            if f.exists(): rows[str(f)]=sha(f)
    return rows
before=snapshot()
(packet/'inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')
changes=subprocess.check_output(['git','diff'],cwd=owner,text=True)
(packet/'owner-draft.json').write_text(json.dumps({'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=owner,text=True).strip(),'diff':changes},indent=2)+'\n')
rebuild={pathlib.Path(*m.split('.')) for m in modules}
def populate(src,dst):
    dst.mkdir(parents=True,exist_ok=True)
    for item in src.iterdir():
        rel=item.relative_to(lib)
        if item.is_dir() and any(rel in f.parents for f in rebuild): populate(item,dst/item.name)
        elif not item.is_dir() and any(rel.parent==f.parent and rel.name.startswith(f.name+'.') for f in rebuild): continue
        else:
            out=dst/item.name
            if not out.exists(): out.symlink_to(item,target_is_directory=item.is_dir())
populate(lib,overlay)
for m in modules:
    out=local/pathlib.Path(*m.split('.')).with_suffix('.lean')
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_bytes(sources[m].read_bytes())
    assert sha(out)==before[str(sources[m])]
os.environ['LEAN_NUM_THREADS']='3'
os.environ['LEAN_PATH']=str(overlay)+':'+str(lib)+':'+os.environ['LEAN_PATH']
commands=[]
def run(name,argv):
    t=time.monotonic()
    print('START',name,flush=True)
    completed=subprocess.run([str(a) for a in argv],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=240)
    record={'name':name,'argv':[str(a) for a in argv],'exit':completed.returncode,'seconds':round(time.monotonic()-t,3),'output':completed.stdout}
    commands.append(record)
    (packet/(name+'.log')).write_text(completed.stdout)
    print('END',name,completed.returncode,completed.stdout[:12000],flush=True)
    return completed.returncode==0
ok=True
for m in modules:
    f=pathlib.Path(*m.split('.'))
    if not run('compile-'+m.rsplit('.',1)[-1],['lean','-M6144','-DwarningAsError=true','-R',local,'-o',overlay/f.with_suffix('.olean'),local/f.with_suffix('.lean')]):
        ok=False; break
if ok: ok=run('audit',['lean','-M6144','-DwarningAsError=true',packet/'Audit.lean'])
after=snapshot()
changed=[p for p in before.keys()|after.keys() if before.get(p)!=after.get(p)]
(packet/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
record={'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'owner_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=owner,text=True).strip(),
    'review_parent':subprocess.check_output(['git','rev-parse','HEAD'],cwd=review,text=True).strip(),
    'source_module_count':len(sources),'changed_inputs':changed,'commands':commands,'lean_path':os.environ['LEAN_PATH'],
    'limits':['Two proof modules independently rebuilt from copied source; other imports reuse owner compiled artifacts',
        'Sources and imported artifacts hashed before and after; no full rebuild or behavior gate',
        'Reconstruction claims retain successful-printing and readable-program premises']}
(packet/'checked-results.json').write_text(json.dumps(record,indent=2)+'\n')
print('CHANGED_INPUTS',changed,flush=True)
raise SystemExit(0 if ok and not changed else 1)
