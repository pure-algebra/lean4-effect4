from pathlib import Path
import datetime,hashlib,json,subprocess
r=Path(__file__).resolve().parent
review=r.parents[2]
primary=Path('/Users/pooks/Dev/lean4-effect4')
commit='ec08fe863bb336f8d77c2287c811266886ef718e'
roots=[primary/'.lake/build/lib/lean']+sorted((primary/'.lake/packages').glob('*/.lake/build/lib/lean'))
overlay=review/'.lake/service-repair-overwatch';overlay.mkdir(exist_ok=True)
todo=['Test.Codegen.ServicesPrint','ProofGraph.AxiomAudit','Effect4.Api'];seen={};std=set()
while todo:
 name=todo.pop()
 if name in seen or name in std:continue
 path=Path(*name.split('.'))
 base=next((base for base in roots if (base/path.with_suffix('.olean')).exists()),None)
 if base is None:
  assert name in ['Init','Std','Lean'] or name.startswith(('Init.','Std.','Lean.')),name
  std.add(name);continue
 p=base/path.with_suffix('.olean');ilean=p.with_suffix('.ilean')
 assert ilean.exists(),name
 todo += [i[0] for i in json.loads(ilean.read_text())['directImports']]
 seen[name]=p
artifacts=[]
for name,p in sorted(seen.items()):
 dst=overlay/Path(*name.split('.')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 for src in [p,p.with_suffix('.ilean'),Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir'),p.with_suffix('.ir.sig')]:
  if not src.exists():continue
  target=dst.parent/src.name;before=src.stat()
  subprocess.run(['cp','-c',str(src),str(target)],check=True)
  digest=hashlib.sha256(target.read_bytes()).hexdigest();after=src.stat()
  assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns),str(src)
  artifacts.append({'module':name,'source':str(src),'target':str(target.relative_to(review)),'sha256':digest,'bytes':target.stat().st_size})
modules=[('src','Effect4.Codegen.Print'),('src','Effect4.Codegen.Read'),('src','Effect4.Library.Semaphore.Defs'),('src','Effect4.Laws.Codegen.Services'),('src','Effect4.Laws.Codegen.Module'),('','Test.Codegen.ServicesPrint')]
files=[str(Path(prefix)/Path(*name.split('.')).with_suffix('.lean')) for prefix,name in modules]
files += ['src/Effect4/Laws/Program/TyView.lean','tools/ProofGraph/AxiomAudit.lean','AGENTS.md','docs/research/2026-10-09-co6b-service-plan.md']
sources=[]
for name in files:
 data=subprocess.check_output(['git','show',commit+':'+name],cwd=primary)
 p=r/'snapshot'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 sources.append({'path':name,'sha256':hashlib.sha256(data).hexdigest()})
(r/'pins.json').write_text(json.dumps({'reviewed_commit':commit,'captured_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'primary_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=primary,text=True).strip(),'toolchain':(primary/'lean-toolchain').read_text().strip(),'artifact_origin':'Copied builder dependencies; changed source modules independently recompiled by compile.py. Uncommitted TyView dependency tracked separately.','sources':sources,'artifacts':artifacts,'standard_library':sorted(std)},indent=2)+'\n')
print(json.dumps({'modules':len(seen),'artifact_megabytes':sum(a['bytes'] for a in artifacts)/1e6}))
