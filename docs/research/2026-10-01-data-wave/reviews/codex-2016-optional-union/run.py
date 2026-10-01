from pathlib import Path
import subprocess, json, hashlib, os, time
p=Path(__file__).parent
repo=Path('/Users/pooks/Dev/lean4-effect4')
rev='4bb22835b13b793e7b0c6fab4360ef2e91cc8ad3'
def pincheck():
 subprocess.run(['git','diff','--quiet',rev,'--','vendor/effect-4.0.0-rc.112'],cwd=repo,check=True)
pincheck()
runs=[]
for label,red in [('green',False),('red',True),('restored',False)]:
 env=dict(os.environ,UV_THREADPOOL_SIZE='1')
 if red:env['REJECT_FALSE_CLAIM']='1'
 start=time.monotonic(); maximum_rss=0; killed=None
 with (p/(label+'.log')).open('w') as log:
  try:
   result=subprocess.run(['bun','--smol',str(p/'probe.mjs')],cwd=p,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=20)
   code=result.returncode
  except subprocess.TimeoutExpired:
   killed='time_bound';code=-1
 runs.append({'label':label,'command':['bun','--smol',str(p/'probe.mjs')],'red_environment':red,'exit_code':code,'elapsed_seconds':round(time.monotonic()-start,3),'runtime_reported_rss_bytes':json.loads((p/(label+'.log')).read_text().splitlines()[0])['memory']['rss'] if (p/(label+'.log')).read_text().startswith('{') else None,'terminated':killed})
 print(label,code,(p/(label+'.log')).read_text()[:1800])
 if (not red and code!=0) or killed:break
pincheck()
(p/'verification.json').write_text(json.dumps({'revision':rev,'vendor_matches_reviewed_commit_before_after':True,'bun':subprocess.check_output(['bun','--version'],text=True).strip(),'limits':{'timeout_seconds_per_run':20,'memory_measurement':'runtime self-report; OS RSS monitoring unavailable in sandbox','serial_runs':True},'source_sha256':{n:hashlib.sha256((repo/'vendor/effect-4.0.0-rc.112/src'/n).read_bytes()).hexdigest() for n in ['Schema.ts','SchemaAST.ts']},'script_sha256':hashlib.sha256((p/'probe.mjs').read_bytes()).hexdigest(),'runs':runs,'scope':'Finite runtime probe from pinned vendored sources; no Lean or TypeScript compiler run','setup_note':'OS resource-limit setup and ps monitoring unavailable in sandbox; finite host probe uses timeout and bun --smol; no compiler process invoked.'},indent=2)+'\n')
