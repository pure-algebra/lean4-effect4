#!/usr/bin/env python3
"""Use the existing interface selector, then compile a scratch lane and all facades."""
from pathlib import Path
import json
import re
import subprocess
import shutil

HERE=Path(__file__).resolve().parent
WT=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
BUILD=HERE/'_build/default'
OUT=HERE/'b5'
OUT.mkdir(exist_ok=True)
logs=[]
def run(cmd):
    r=subprocess.run([str(c) for c in cmd],cwd=OUT,text=True,capture_output=True)
    logs.append({'command':[str(c) for c in cmd],'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
    return r.returncode

old=WT/'ocaml/engine/test/lanes/lanes_gen.mli'
roots=','.join(re.findall(r'^val (\w+)',old.read_text(),re.M))
run([BUILD/'gen/interface/main.exe',BUILD/'engine/test/lanes/.effect4_lanes.objs/byte/lanes_gen.cmt',
     OUT/'lanes_gen.mli',roots,'','','reachable'])
includes=[]
for d in ['eff/.effect4_eff.objs/byte','clock/.effect4_clock.objs/byte',
          'lcnf/.effect4_lcnf.objs/byte','gen/.effect4_closure.objs/byte']:
    includes+=['-I',BUILD/d]
cmd=['opam','exec','--switch=effect4','--','ocamlfind','ocamlopt','-package','zarith',*includes,'-w','@55','-c']
run(cmd+['lanes_gen.mli'])
shutil.copyfile(WT/'ocaml/engine/test/lanes/lanes_gen.ml',OUT/'lanes_gen.ml')
run(cmd+['lanes_gen.ml'])
for lane in ['todo','ctors','modeled','rocq']:
    for ext in ['mli','ml']:
        name=lane+'_gen.'+ext
        shutil.copyfile(WT/'ocaml/engine/test'/lane/name,OUT/name)
        run(cmd+[name])
(OUT/'compile.json').write_text(json.dumps(logs,indent=2)+'\n')
print('lanes interface lines',len(old.read_text().splitlines()),'->',len((OUT/'lanes_gen.mli').read_text().splitlines()))
for row in logs: print(row['command'][-1],row['exit'],row['stderr'][:500])
