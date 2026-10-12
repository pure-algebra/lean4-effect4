from pathlib import Path
import os,shutil,subprocess,sys
root=Path.cwd()
space=Path('/private/tmp/effect4-place-counter-current');space.mkdir(exist_ok=True)
for src,dst in [
 (root/'docs/research/2026-10-11-machine-models/codex/operation-count/OperationCounterLedgerProbe.lean','OperationCounterLedgerProbe.lean'),
 (root/'docs/research/2026-10-11-machine-models/codex/place-funding/OperationCounterCommandProbe.lean','OperationCounterCommandProbe.lean'),
 (root/'docs/research/2026-10-11-machine-models/codex/place-funding/OperationCounterStepProbe.lean','OperationCounterStepProbe.lean')]:
 shutil.copyfile(src,space/dst)
(space/'CounterAudit.lean').write_text('import OperationCounterStepProbe\nimport ProofGraph.AxiomAudit\n#axiom_audit OperationCounterLedgerProbe OperationCounterCommandProbe OperationCounterStepProbe\n')
env=os.environ.copy();env['LEAN_PATH']=str(space)+os.pathsep+env.get('LEAN_PATH','');env['LEAN_NUM_THREADS']='3'
for name in ['OperationCounterLedgerProbe','OperationCounterCommandProbe','OperationCounterStepProbe','CounterAudit']:
 args=['lean','--root='+str(space),'-DwarningAsError=true','-o',str(space/(name+'.olean')),str(space/(name+'.lean'))]
 log=space/(name+'.log')
 with log.open('w') as out:
  print('COMMAND:',' '.join(args),file=out,flush=True)
  result=subprocess.run(args,env=env,stdout=out,stderr=subprocess.STDOUT)
 print(name, 'PASS' if result.returncode==0 else 'FAIL',flush=True)
 if result.returncode or name=='CounterAudit':print(log.read_text(),flush=True)
 if result.returncode:sys.exit(result.returncode)
