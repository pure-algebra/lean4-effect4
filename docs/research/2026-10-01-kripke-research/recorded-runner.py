import importlib.util,json,pathlib,subprocess,time,os,signal,hashlib,contextlib
ROOT=pathlib.Path('/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4')
OUT=pathlib.Path(__file__).parent
spec=importlib.util.spec_from_file_location('guard',ROOT/'scripts/check-semantics.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
receipt={'commands':[],'scope':'read-only prepared-source and saved-artifact checks; isolated research proof','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()}
try:
 with (OUT/"preflight.log").open("w") as output, contextlib.redirect_stdout(output):
  guard.require_artifacts(receipt)
 receipt['probeSha256']=hashlib.sha256((OUT/'KripkeProbe.lean').read_bytes()).hexdigest()
 cmd=['lake','env','lean','-j1','-M4096','-DwarningAsError=true',str(OUT/'KripkeProbe.lean')]
 start=time.monotonic()
 with (OUT/'probe.log').open('w') as stream:
  process=subprocess.Popen(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,env={**os.environ,'LEAN_NUM_THREADS':'1'},start_new_session=True)
  try: process.wait(timeout=180)
  except subprocess.TimeoutExpired:
   os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=10)
 receipt['probe']={'command':cmd,'exit':process.returncode,'seconds':round(time.monotonic()-start,3)}
 receipt['result']='passed' if process.returncode==0 else 'failed'
except Exception as exc:
 receipt['result']='failed';receipt['error']=str(exc)
finally:
 (OUT/'probe-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:v for k,v in receipt.items() if k not in ['savedOutputs','commands']},indent=2))
 if (OUT/'probe.log').exists():print((OUT/'probe.log').read_text())
