from pathlib import Path
import os,subprocess,json,sys
root=Path.cwd(); folder=root/'docs/research/2026-10-11-machine-models/codex/callback-loop'
env=dict(os.environ,LEAN_NUM_THREADS='3')
env=json.loads(subprocess.check_output(['lake','env','python3','-c','import os,json;print(json.dumps(dict(os.environ)))'],cwd=root,env=env))
env['LEAN_PATH']=str(folder)+':'+env.get('LEAN_PATH','')
names=['CountdownJoinProbe','TimeoutJointGenerationProbe','TimeoutRootLoopProbe','TimeoutNativeRootFamilyProbe','TimeoutReadyEntryProbe','TimeoutRaceOwnershipProbe','TimeoutRaceWaitingProbe','TimeoutCancelPhaseProbe','TimeoutRaceSettleProbe']
for name in names:
 args=['lean','--root='+str(folder),'-DwarningAsError=true','-o',str(folder/(name+'.olean')),str(folder/(name+'.lean'))]
 log=Path('/private/tmp/timeout-waiting-'+name+'.log')
 with log.open('w') as out:
  print('COMMAND:',' '.join(args),file=out,flush=True)
  result=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
 print(name,result.returncode,flush=True)
 if result.returncode: print(log.read_text());sys.exit(result.returncode)
args=['lean','-DwarningAsError=true',str(folder/'WaitingAudit.lean')]
log=Path('/private/tmp/timeout-waiting-audit.log')
with log.open('w') as out:
 print('COMMAND:',' '.join(args),file=out,flush=True)
 result=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
print(log.read_text());sys.exit(result.returncode)
