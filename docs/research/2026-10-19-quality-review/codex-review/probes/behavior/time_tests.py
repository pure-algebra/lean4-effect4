from pathlib import Path
import os,json,subprocess,time,csv,re
P=Path(__file__).resolve().parent; B=P.parent/'_build/default'; W=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
(P/'tmp').mkdir(exist_ok=True);(P/'timings').mkdir(exist_ok=True)
env=dict(os.environ,TMPDIR=str(P/'tmp'),E4_LEAN_CORPUS='/Users/pooks/Dev/lean4-effect4/.lake/corpus',E4_EFF_GOLDENS=str(W/'ocaml/eff/goldens'),E4_HEX_GOLDENS=str(W/'ocaml/goldens/eff'),E4_TRUTH_CORPUS=str(W/'harness/truth/corpus.json'))
rows=[]
exes=sorted(p for p in B.rglob('*.exe') if p.name.startswith(('test_','prop_','stm_')))
for p in exes:
 relative=p.relative_to(B); cwd=W/'ocaml'/relative.parent
 if not cwd.exists():continue
 t=time.monotonic()
 try:
  r=subprocess.run([str(p)],capture_output=True,text=True,timeout=30,cwd=cwd,env=env)
  status=r.returncode;log=r.stdout+r.stderr
 except subprocess.TimeoutExpired as e:status='timeout30';log=(e.stdout or b'').decode(errors='replace')+(e.stderr or b'').decode(errors='replace')
 secs=time.monotonic()-t
 (P/'timings'/str(relative).replace('/','_')).with_suffix('.log').write_text(log)
 rows.append(dict(test=str(relative),seconds=secs,status=status,cwd=str(cwd)))
 print(str(relative),round(secs,3),status,flush=True)
 (P/'test-times.json').write_text(json.dumps(dict(environment={k:env[k] for k in ['TMPDIR','E4_LEAN_CORPUS','E4_EFF_GOLDENS','E4_HEX_GOLDENS','E4_TRUTH_CORPUS']},rows=rows),indent=2))
