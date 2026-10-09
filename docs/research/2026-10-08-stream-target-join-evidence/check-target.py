#!/usr/bin/env python3
"""Finite exact old/candidate target check; no module or compiler theorem."""
from pathlib import Path
import argparse,json,shutil,subprocess
p=argparse.ArgumentParser()
p.add_argument('--install',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args(); here=Path(__file__).resolve().parent
out=a.out.resolve(); out.mkdir(parents=True,exist_ok=False)
install=a.install.resolve()
for name,version in [('effect','4.0.1'),('@typescript/native-preview','7.0.0-dev.20260629.1')]:
    assert json.loads((install/name/'package.json').read_text())['version']==version
(out/'node_modules').symlink_to(install,target_is_directory=True)
for name in ['old.ts','candidate.ts','prelude.ts','prelude-atoms.gen.ts','records.ts','tuples.ts','observe.mjs']:
    shutil.copyfile(here/name,out/name)
compiler=['node',str(install/'@typescript/native-preview/bin/tsgo')]
version=subprocess.check_output(compiler+['--version'],text=True).strip()
assert version=='Version 7.0.0-dev.20260629.1'
for name in ['old','candidate']:
    shutil.copyfile(here/(name+'-tsconfig.json'),out/(name+'-tsconfig.json'))
    r=subprocess.run(compiler+['--pretty','false','--noEmit','-p',str(out/(name+'-tsconfig.json'))],cwd=out,capture_output=True,text=True)
    (out/(name+'-diagnostics.log')).write_text(r.stdout+r.stderr)
    assert (r.returncode==0)==(name=='candidate')
    if name=='old': assert 'TS2375' in r.stdout+r.stderr
    print(name+': compiler exit '+str(r.returncode))
r=subprocess.run(['bun','--no-install','observe.mjs'],cwd=out,capture_output=True,text=True,check=True)
assert json.loads(r.stdout)==[['Chunk',[1,2,3]],['End',None],None]
(out/'observations.json').write_text(r.stdout)
print(r.stdout,end='')
