import subprocess, tempfile, shutil
from pathlib import Path
r=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
with tempfile.TemporaryDirectory(prefix='seams-warning32-') as d:
 d=Path(d)
 for n in ['eff_types.ml','eff_types.mli']:
  shutil.copyfile(r/'ocaml/eff'/n,d/n)
 for n in ['api_gen.ml','api_gen.mli']:
  shutil.copyfile(r/'ocaml/gen'/n,d/n)
 base=['opam','exec','--switch=effect4','--','ocamlopt','-I',str(d)]
 for p in ['clock/.effect4_clock.objs/byte','lcnf/.effect4_lcnf.objs/byte']:
  base+=['-I',str(r/'ocaml/_build/default'/p)]
 for n in ['eff_types.mli','eff_types.ml','api_gen.mli']:
  subprocess.run([*base,'-w','@55','-c',str(d/n)],cwd=d,check=True)
 a=subprocess.run([*base,'-w','@32@55','-c',str(d/'api_gen.ml')],cwd=d,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(a.stdout)
 print('status',a.returncode)
 assert a.returncode==2 and 'warning 32' in a.stdout
