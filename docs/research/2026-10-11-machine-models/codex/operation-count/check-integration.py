from pathlib import Path
import subprocess,os,sys,json,re
root=Path.cwd(); base=root/'docs/research/2026-10-11-machine-models/codex'; probes=base/'callback-loop'; counts=base/'operation-count'
env=dict(os.environ,LEAN_NUM_THREADS='3')
changed=['Effect4.Laws.Program.Footprint','Effect4.Laws.Program.Interference','Effect4.Laws.Machine.EditObserverWords','Effect4.Laws.Program.NativeConfiguration','Effect4.Laws.Program.NativeEvaluation','Effect4.Laws.Program.NativeActions','Effect4.Laws.Machine.Clauses']
mods=set(changed)
for directory in ['src','Test','tools']:
 for path in (root/directory).rglob('*.lean'):
  imports=re.findall(r'^import (\S+)',path.read_text(),re.M)
  if not set(imports).intersection(changed):continue
  rel=path.relative_to(root/directory) if directory in ['src','tools'] else path.relative_to(root)
  module='.'.join(rel.with_suffix('').parts)
  if module in ['Effect4','Effect4.Laws','Test.All']:continue
  mods.add(module)
mods.add('Test.Dogfood.Proofs.HostTimeoutNumberCounted')
def run(label,args,active_env=env):
 log=Path('/private/tmp/count-race-integration-'+label+'.log')
 with log.open('w') as out:
  print('COMMAND:',' '.join(args),file=out,flush=True)
  result=subprocess.run(args,cwd=root,env=active_env,stdout=out,stderr=subprocess.STDOUT)
 print(label,result.returncode,flush=True)
 if result.returncode:print(log.read_text());sys.exit(result.returncode)
run('build',['lake','build']+sorted(mods))
leanenv=json.loads(subprocess.check_output(['lake','env','python3','-c','import os,json;print(json.dumps(dict(os.environ)))'],cwd=root,env=env))
leanenv['LEAN_PATH']=str(probes)+':'+leanenv.get('LEAN_PATH','')
for name in ['CountdownJoinProbe','TimeoutJointGenerationProbe','TimeoutRaceOwnershipProbe']:
 run(name,['lean','--root='+str(probes),'-DwarningAsError=true','-o',str(probes/(name+'.olean')),str(probes/(name+'.lean'))],leanenv)
run('race-audit',['lean','-DwarningAsError=true',str(probes/'RaceOwnershipAudit.lean')],leanenv)
run('count-audit',['lean','-DwarningAsError=true',str(counts/'Audit.lean')],leanenv)
