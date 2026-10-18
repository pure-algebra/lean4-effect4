from pathlib import Path
import os,sys,subprocess,json,re
p=Path('/private/tmp/seams-s1-ledger');s1=Path('/private/tmp/seams-check-sol/s1-full');r=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4');mode=sys.argv[1];lib=p/'lib/lean';lib.mkdir(parents=True,exist_ok=True)
for root in [s1/'lib/lean',r/'.lake/build/lib/lean']:
 for f in root.rglob('*'):
  if f.is_file():
   target=lib/f.relative_to(root);target.parent.mkdir(parents=True,exist_ok=True)
   if not target.exists() and not target.is_symlink():target.symlink_to(f)
if mode=='red':
 cmd=['lean','-DwarningAsError=true',str(p/'LedgerControl.lean')];z=subprocess.run(cmd,env={**os.environ,'LEAN_PATH':str(s1/'lib/lean')+':'+os.environ['LEAN_PATH']},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(p/'red.log').write_text(z.stdout);print(z.stdout);assert z.returncode!=0 and 'did not evaluate' in z.stdout;raise SystemExit(0)
order=json.loads((s1/'order.json').read_text())
texts={}
for root in [r/'src',r/'tools',r/'Test',s1/'src']:
 for f in root.rglob('*.lean'):
  module=str(f.relative_to(root).with_suffix('')).replace('/','.')
  if root==r/'Test':module='Test.'+module
  texts[module]=f.read_text()
affected={}
def needs(module):
 if module in affected:return affected[module]
 affected[module]=False
 affected[module]=module=='Effect4.Program.Typing.SourceDocument' or any(needs(x) for x in re.findall(r'^(?:public )?import\s+([\w.]+)',texts.get(module,''),re.M))
 return affected[module]
order=[n for n in order if needs(n)]
(p/'order.json').write_text(json.dumps(order,indent=2)+'\n')
for module in order:
 rel=Path(*module.split('.'));src=p/'src'/rel.with_suffix('.lean')
 if not src.exists():
  original=s1/'src'/rel.with_suffix('.lean');assert original.exists(),original;src.parent.mkdir(parents=True,exist_ok=True);src.write_bytes(original.read_bytes())
 out=lib/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.olean.private','.olean.server','.ir','.ir.sig']:
  q=lib/rel.with_suffix(suffix)
  if q.is_symlink():q.unlink()
 z=subprocess.run(['lean','-DwarningAsError=true','--root='+str(p/'src'),'-o',str(out),str(src)],env={**os.environ,'LEAN_PATH':str(lib)+':'+os.environ['LEAN_PATH']},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=p/'logs'/rel.with_suffix('.log');log.parent.mkdir(parents=True,exist_ok=True);log.write_text(z.stdout);print(module,z.returncode,z.stdout[-5000:] if z.returncode else '',flush=True)
 if z.returncode:raise SystemExit(z.returncode)
z=subprocess.run(['lean','-DwarningAsError=true',str(p/'LedgerControl.lean')],env={**os.environ,'LEAN_PATH':str(lib)+':'+os.environ['LEAN_PATH']},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(p/'green.log').write_text(z.stdout);print(z.stdout);raise SystemExit(z.returncode)
