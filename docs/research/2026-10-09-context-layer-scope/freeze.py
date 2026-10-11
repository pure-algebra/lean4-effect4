from pathlib import Path
import datetime,hashlib,json,subprocess
r=Path(__file__).resolve().parent; review=r.parents[2]
if (r/'pins.json').exists():
 raise SystemExit('Refusing to overwrite retained evidence; create a new capture directory.')
primary=Path('/Users/pooks/Dev/lean4-effect4')
overlay=review/'.lake/context-layer-scope'; overlay.mkdir(exist_ok=True)
roots=[primary/'.lake/build/lib/lean']+sorted((primary/'.lake/packages').glob('*/.lake/build/lib/lean'))
todo=['Effect4.Program.Compile','Effect4.Program.Authoring','Effect4.Program.Definitions'];seen={};std=set()
while todo:
 name=todo.pop()
 if name in seen or name in std:continue
 path=Path(*name.split('.')).with_suffix('.olean')
 base=next((b for b in roots if (b/path).exists()),None)
 if base is None:
  assert name in ['Init','Std','Lean'] or name.startswith(('Init.','Std.','Lean.')),name
  std.add(name);continue
 p=base/path;todo.extend(x[0] for x in json.loads(p.with_suffix('.ilean').read_text())['directImports']);seen[name]=p
artifacts=[]
for name,p in sorted(seen.items()):
 dst=overlay/Path(*name.split('.')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 for src in [p,p.with_suffix('.ilean'),Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir'),p.with_suffix('.ir.sig')]:
  if not src.exists():continue
  before=src.stat();target=dst.parent/src.name
  subprocess.run(['cp','-c',str(src),str(target)],check=True)
  after=src.stat();assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns),str(src)
  artifacts.append({'module':name,'source':str(src),'target':str(target.relative_to(review)),'sha256':hashlib.sha256(target.read_bytes()).hexdigest()})
files=['AGENTS.md','docs/research/2026-10-09-program-parameters.md','src/Effect4/Program/Compile.lean','src/Effect4/Machine/Stores.lean','src/Effect4/Program/Eff.lean','src/Effect4/Program/Native.lean','src/Effect4/Program/Definitions.lean','src/Effect4/Program/Authoring.lean','src/Effect4/Program/Typing/Focus.lean','src/Effect4/Laws/Program/Typed/Admission.lean','src/Effect4/Laws/Program/Typed/Denotation.lean','src/Effect4/Laws/Program/DenoteR.lean','src/Effect4/Library/Pool/Ops.lean','src/Effect4/Laws/Library/Pool/Ops.lean','src/Effect4/Library/Waiting.lean','tools/ProofGraph/Registry.lean']
sources=[]
for name in files:
 data=(primary/name).read_bytes();dst=r/'snapshot'/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 sources.append({'path':name,'sha256':hashlib.sha256(data).hexdigest(),'git_blob':subprocess.check_output(['git','hash-object','--stdin'],input=data,cwd=primary).decode().strip()})
pin={'captured_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'primary_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=primary,text=True).strip(),'review_base':subprocess.check_output(['git','rev-parse','HEAD'],cwd=review,text=True).strip(),'scope':'Live work in progress, not a claimed landing. Captured builder dependencies; Compile independently checked from retained source.','sources':sources,'artifacts':artifacts,'standard_library':sorted(std),'primary_changes':subprocess.check_output(['git','status','--short'],cwd=primary,text=True).splitlines()}
(r/'pins.json').write_text(json.dumps(pin,indent=2)+'\n')
print('Captured',len(seen),'dependency modules and',len(sources),'source files.')
