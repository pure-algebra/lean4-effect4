from pathlib import Path
import subprocess,os,sys,json
root=Path.cwd(); probes=root/'docs/research/2026-10-11-machine-models/codex/callback-loop'
env=dict(os.environ,LEAN_NUM_THREADS='3')
def run(label,args,env=env):
 log=Path('/private/tmp/timeout-callback-integration-'+label+'.log')
 with log.open('w') as out:
  print('COMMAND:',' '.join(args),file=out,flush=True)
  result=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
 print(label,result.returncode,flush=True)
 if result.returncode: print(log.read_text());sys.exit(result.returncode)
run('build',['lake','build','Effect4.Laws.Contracts.FramePath','Effect4.Laws.Machine.AnswerFlow','Effect4.Laws.Machine.AnswerFlowFamilyPop','Effect4.Laws.Program.NativeFrameScope','Effect4.Laws.Program.NativeActionScope','Effect4.Laws.Program.Guard.Core','Test.Dogfood.Proofs.HostTimeoutNumberFormFamily'])
leanenv=json.loads(subprocess.check_output(['lake','env','python3','-c','import os,json;print(json.dumps(dict(os.environ)))'],cwd=root,env=env))
leanenv['LEAN_PATH']=str(probes)+':'+leanenv.get('LEAN_PATH','')
for name in ['CountdownJoinProbe','TimeoutJointGenerationProbe','TimeoutRootLoopProbe','TimeoutNativeRootFamilyProbe','TimeoutReadyEntryProbe']:
 run(name,['lean','--root='+str(probes),'-DwarningAsError=true','-o',str(probes/(name+'.olean')),str(probes/(name+'.lean'))],leanenv)
run('audit',['lean','-DwarningAsError=true',str(probes/'Audit.lean')],leanenv)
