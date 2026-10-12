from pathlib import Path
import os,subprocess,sys
root=Path.cwd();folder=root/'docs/research/2026-10-11-machine-models/codex/callback-loop'
env=os.environ.copy();env['LEAN_PATH']=str(folder)+os.pathsep+env.get('LEAN_PATH','');env['LEAN_NUM_THREADS']='3'
# Earlier unchanged local readers already exist from the accepted waiting integration.
for name in ['TimeoutReadyEntryProbe','TimeoutRaceOwnershipProbe','TimeoutRaceWaitingProbe','TimeoutCancelPhaseProbe','TimeoutRaceSettleProbe']:
 args=['lean','--root='+str(folder),'-DwarningAsError=true','-o',str(folder/(name+'.olean')),str(folder/(name+'.lean'))]
 log=Path('/private/tmp/head-integration-'+name+'.log')
 with log.open('w') as out:
  print('COMMAND:',' '.join(args),file=out,flush=True)
  result=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
 print(name, 'PASS' if result.returncode==0 else 'FAIL',flush=True)
 if result.returncode: print(log.read_text());sys.exit(result.returncode)
audit=folder/'HeadAudit.lean'
args=['lean','-DwarningAsError=true',str(audit)]
log=Path('/private/tmp/head-integration-audit.log')
with log.open('w') as out:
 print('COMMAND:',' '.join(args),file=out,flush=True)
 result=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
print(log.read_text());sys.exit(result.returncode)
