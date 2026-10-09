from pathlib import Path
import subprocess,os,json,hashlib,time
repo=Path('/Users/pooks/Dev/lean4-effect4')
out=Path('/tmp/effect4-duplicate-overwatch-0647')
rev='7334f1197cf5b535541ce1dfc7789a5082c07115'
files=['src/Effect4/Laws/Library/Semaphore/Data.lean','src/Effect4/Laws/Library/Pool/Ops.lean','src/Effect4/Laws/Codegen/PrintTyped.lean','Test/Program/RegistrationYield.lean']
mods=[p.removeprefix('src/').removesuffix('.lean') for p in files]
manifest={'base':'7b73d59cb2ae5b290c87c7f0ba9a6aa77a71fa04','head':rev,'sources':{},'checks':[]}
for rel in files:
 data=subprocess.check_output(['git','show',f'{rev}:{rel}'],cwd=repo)
 dest=out/'source'/rel
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 manifest['sources'][rel]={'sha256':hashlib.sha256(data).hexdigest(),'matchesPrimary':data==(repo/rel).read_bytes()}
overlay=out/'overlay'; base=repo/'.lake/build/lib/lean'
def links(src,dst,rel=''):
 dst.mkdir(parents=True,exist_ok=True)
 for child in src.iterdir():
  key=f'{rel}/{child.name}'.lstrip('/')
  dest=dst/child.name
  if child.is_dir() and any(m.startswith(key+'/') for m in mods):links(child,dest,key)
  elif any(key.startswith(m+'.') for m in mods):continue
  elif not dest.exists() and not dest.is_symlink():dest.symlink_to(child,target_is_directory=child.is_dir())
links(base,overlay)
libs=[overlay,base,*sorted((repo/'.lake/packages').glob('*/.lake/build/lib/lean'))]
env={**os.environ,'LEAN_NUM_THREADS':'3','LEAN_PATH':':'.join(map(str,libs))}
lean=Path('/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
manifest.update(compiler=str(lean),compilerSHA256=hashlib.sha256(lean.read_bytes()).hexdigest(),LEAN_NUM_THREADS='3',LEAN_PATH=env['LEAN_PATH'])
for rel,mod in zip(files,mods):
 dest=overlay/f'{mod}.olean';dest.parent.mkdir(parents=True,exist_ok=True)
 cwd=out/'source/src' if rel.startswith('src/') else out/'source'
 cmd=[str(lean),'-DwarningAsError=true','-o',str(dest),mod+'.lean']
 start=time.monotonic();p=subprocess.run(cmd,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=mod.replace('/','-')+'.log';(out/log).write_text(p.stdout)
 manifest['checks'].append({'command':cmd,'cwd':str(cwd),'exitCode':p.returncode,'seconds':round(time.monotonic()-start,3),'log':log})
 (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(f'{mod}: exit {p.returncode}',flush=True)
 if p.returncode:
  print(p.stdout,flush=True);raise SystemExit(p.returncode)
