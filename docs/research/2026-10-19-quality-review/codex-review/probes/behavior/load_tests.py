from pathlib import Path
import subprocess,os,time,json,signal
P=Path(__file__).resolve().parent;exe=P.parent/'_build/default/engine/test/stm/stm_admit.exe';script=P.parents[4]/'2026-10-18-slices/w2-engine-mutants/stm_load.py'
script=Path('/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-18-slices/w2-engine-mutants/stm_load.py')
cmd=['python3',str(script),str(exe),str(P/'stm-load'), '12','5'];t=time.monotonic(); p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env=dict(os.environ,TMPDIR=str(P/'tmp')),start_new_session=True)
try:out,_=p.communicate(timeout=90);status=p.returncode
except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);out,_=p.communicate();status='timeout90'
r=dict(command=cmd,status=status,seconds=time.monotonic()-t,output=out);(P/'load-tests.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
