from pathlib import Path
import os,json,subprocess,time
P=Path(__file__).resolve().parent; B=P.parent/'_build/default'; W=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
env=dict(os.environ,TMPDIR=str(P/'tmp'),E4_LEAN_CORPUS='/Users/pooks/Dev/lean4-effect4/.lake/corpus',E4_EFF_GOLDENS=str(W/'ocaml/eff/goldens/p42.bin'),E4_HEX_GOLDENS=str(W/'ocaml/goldens/eff/p42.hex'),E4_TRUTH_CORPUS=str(W/'harness/truth/corpus.json'))
prior=json.loads((P/'test-times.json').read_text()); rows=[]
for old in prior['rows']:
 if old['status']==0:continue
 rel=Path(old['test']);args=[]
 if rel.name=='test_lean_wire.exe':args=[W/'ocaml/goldens/eff']
 if rel.name=='test_interface.exe':args=[B/'gen/interface/fixture.cmt',W/'ocaml/gen/interface/fixture_prelude.ml',B/'gen/interface/fixture_facade.cmt']
 cmd=list(map(str,[B/rel,*args]));t=time.monotonic();r=subprocess.run(cmd,cwd=old['cwd'],env=env,capture_output=True,text=True,timeout=30)
 row=dict(test=str(rel),command=cmd,seconds=time.monotonic()-t,status=r.returncode,cwd=old['cwd']);rows.append(row)
 (P/'timings'/('recheck_'+str(rel).replace('/','_'))).with_suffix('.log').write_text(r.stdout+r.stderr)
 print(row,flush=True)
(P/'test-rechecks.json').write_text(json.dumps(dict(environment={k:v for k,v in env.items() if k.startswith('E4_') or k=='TMPDIR'},rows=rows),indent=2))
