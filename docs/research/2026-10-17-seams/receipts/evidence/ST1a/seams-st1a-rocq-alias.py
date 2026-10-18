from pathlib import Path
import importlib.util,sys,tempfile,json
repo=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
sys.path.insert(0,str(repo/'scripts'))
spec=importlib.util.spec_from_file_location('generator',repo/'scripts/generate.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
with tempfile.TemporaryDirectory(prefix='seams-rocq-alias-') as d:
 r=Path(d)/'root';o=Path(d)/'out';(r/'rocq').mkdir(parents=True);(o/'rocq').mkdir(parents=True)
 expected={'Skeleton.v':'skeleton','StoreCode.v':'code'}
 for n,v in expected.items():(r/'rocq'/n).write_text(v)
 (o/'rocq/Skeleton.v').symlink_to(r/'rocq/StoreCode.v')
 commands=[]
 def run(cmd,*args):
  commands.append(cmd)
  if cmd[:3]==['lake','env','lean']:
   Path(cmd[-2]).write_text('skeleton');Path(cmd[-1]).write_text('code')
 def install(src,dst,checking):
  if checking and src.read_bytes()!=dst.read_bytes(): raise ValueError('drift')
 g.ROOT=r;g.run=run;g.install=install
 error=None
 try:g.store_rocq(o,True)
 except ValueError as e:error=str(e)
 unchanged=all((r/'rocq'/n).read_text()==v for n,v in expected.items())
 print(json.dumps({'producer_calls':len(commands),'error':error,'published_unchanged':unchanged}))
 assert error and 'aliases' in error and not commands and unchanged
