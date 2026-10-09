#!/usr/bin/env python3
"""Compile the retained proof sources and run the Queue controls with existing imports."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time
p=argparse.ArgumentParser()
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
repo=a.repo.resolve(); out=a.out.resolve(); evidence=Path(__file__).resolve().parent
if out.exists():
    raise SystemExit('Choose a new output directory.')
out.mkdir(parents=True)
revision=json.loads((evidence/'manifest.json').read_text())['reviewed_commit']
modules=['Effect4/Laws/Program/Address','Effect4/Laws/Auto/ExceptMap','Effect4/Laws/Program/Typing/Annotate','Effect4/Laws/Program/Typing/Rebase']
for module in modules:
    rel=f'src/{module}.lean'
    source=evidence/'source'/rel
    expected=subprocess.check_output(['git','show',f'{revision}:{rel}'],cwd=repo)
    if source.read_bytes()!=expected:
        raise SystemExit(f'Retained source differs from {revision}:{rel}')
    dest=out/'source'/rel
    dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,dest)
shutil.copyfile(evidence/'QueueRebaseProbe.lean',out/'QueueRebaseProbe.lean')
base=repo/'.lake/build/lib/lean'; overlay=out/'overlay'
def link_imports(src,dst,relative=''):
    dst.mkdir(parents=True,exist_ok=True)
    for child in src.iterdir():
        key=f'{relative}/{child.name}'.lstrip('/')
        dest=dst/child.name
        if child.is_dir() and any(m.startswith(key+'/') for m in modules):
            link_imports(child,dest,key)
        elif any(key.startswith(m+'.') for m in modules):
            continue
        else:
            dest.symlink_to(child,target_is_directory=child.is_dir())
link_imports(base,overlay)
lean=Path.home()/'.elan/toolchains'/((repo/'lean-toolchain').read_text().strip().replace('/','--').replace(':','---'))/'bin/lean'
libs=[overlay,base,*sorted((repo/'.lake/packages').glob('*/.lake/build/lib/lean'))]
env={**os.environ,'LEAN_NUM_THREADS':'3','LEAN_PATH':':'.join(map(str,libs))}
results=[]
def run(cmd,cwd,log):
    start=time.monotonic()
    result=subprocess.run(cmd,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (out/log).write_text(result.stdout)
    results.append({'command':list(map(str,cmd)),'cwd':str(cwd),'exit':result.returncode,'log':log,'seconds':round(time.monotonic()-start,3)})
    (out/'results.json').write_text(json.dumps({'reviewed_commit':revision,'LEAN_NUM_THREADS':'3','LEAN_PATH':env['LEAN_PATH'],'checks':results},indent=2)+'\n')
    print(f'{log}: exit {result.returncode}',flush=True)
    if result.returncode:
        print(result.stdout,flush=True)
        raise SystemExit(result.returncode)
for module in modules:
    target=overlay/f'{module}.olean'
    target.parent.mkdir(parents=True,exist_ok=True)
    run([str(lean),'-DwarningAsError=true','-o',str(target),f'{module}.lean'],out/'source/src',Path(module).name+'.compile.log')
run([str(lean),'-DwarningAsError=true','QueueRebaseProbe.lean'],out,'QueueRebaseProbe.log')
print('PASS: exact retained sources, Queue controls, and scoped proof audit.')
