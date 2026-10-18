from pathlib import Path
import importlib.util, tempfile, shutil, json
root=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
p=root/'scripts/lib/store_facts.py'
spec=importlib.util.spec_from_file_location('facts',p)
facts=importlib.util.module_from_spec(spec);spec.loader.exec_module(facts)
with tempfile.TemporaryDirectory(prefix='seams-facts-alias-') as d:
 r=Path(d)/'root';o=Path(d)/'out'
 for rel in facts.FILES:
  (r/rel).parent.mkdir(parents=True,exist_ok=True); (r/rel).write_text('retained '+rel.name)
 rel=facts.FILES[0]; victim=facts.FILES[-1]
 (o/rel).parent.mkdir(parents=True,exist_ok=True); (o/rel).symlink_to(r/victim)
 commands=[]
 def run(cmd):
  commands.append(cmd)
  if cmd[:3]==['lake','env','lean']:
   for x in facts.FILES: (Path(cmd[-1])/x.name).write_text('retained '+x.name)
 def install(src,dst,checking):
  if checking: assert src.read_bytes()==dst.read_bytes()
  else: shutil.copyfile(src,dst)
 before=(r/victim).read_bytes()
 error=None
 try: facts.generate(r,o,True,run,install)
 except ValueError as e: error=str(e)
 print(json.dumps({'producer_calls':len(commands),'error':error,'victim_unchanged':(r/victim).read_bytes()==before}))
 assert error and 'aliases' in error and not commands and (r/victim).read_bytes()==before
