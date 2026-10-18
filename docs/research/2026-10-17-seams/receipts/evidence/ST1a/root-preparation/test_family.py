from pathlib import Path
import importlib.util,json,tempfile,shutil
spec=importlib.util.spec_from_file_location('facts','/private/tmp/seams-st1a/scripts/lib/store_facts.py')
facts=importlib.util.module_from_spec(spec);spec.loader.exec_module(facts)
source=Path('/private/tmp/seams-st1a-root/native-facts')
with tempfile.TemporaryDirectory(prefix='store-facts-controls-') as directory:
 root=Path(directory)/'root'; out=Path(directory)/'check'; commands=[]
 def install(src,dst,checking):
  if checking:
   if not dst.exists() or src.read_bytes()!=dst.read_bytes(): raise ValueError('drift')
  else:
   dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 def run(cmd):
  commands.append(cmd)
  if cmd[:3]==['lake','env','lean']:
   for relative in facts.FILES:shutil.copyfile(source/relative.name,Path(cmd[-1])/relative.name)
 facts.generate(root,out,False,run,install)
 expected={str(p): (root/p).read_bytes() for p in facts.FILES}
 facts.generate(root,out,True,run,install)
 assert all((out/p).read_bytes()==expected[str(p)] for p in facts.FILES)
 before=len(commands)
 try:facts.generate(root,root,True,run,install)
 except ValueError as e:assert 'aliases' in str(e)
 else:raise AssertionError('alias accepted')
 assert len(commands)==before
 def missing(cmd):
  if cmd[:3]==['lake','env','lean']:
   for relative in facts.FILES[:-1]:shutil.copyfile(source/relative.name,Path(cmd[-1])/relative.name)
 try:facts.generate(root,out,False,missing,install)
 except ValueError as e:assert 'no output' in str(e)
 else:raise AssertionError('missing file accepted')
 assert all((root/p).read_bytes()==expected[str(p)] for p in facts.FILES)
 def changed(cmd):
  run(cmd)
  if cmd[:3]==['lake','env','lean']:
   with (Path(cmd[-1])/facts.FILES[-1].name).open('a') as f:f.write('\n(* changed *)\n')
 try:facts.generate(root,out,True,changed,install)
 except ValueError as e:assert str(e)=='drift'
 else:raise AssertionError('drift accepted')
 assert all((root/p).read_bytes()==expected[str(p)] for p in facts.FILES)
 assert all((out/p).read_bytes()==expected[str(p)] for p in facts.FILES)
 print('PASS: fresh install/check, aliases, missing output, and drift before copy')
 print('Scope: Python staging controls use retained real producer output; actual producer command has separate evidence.')
