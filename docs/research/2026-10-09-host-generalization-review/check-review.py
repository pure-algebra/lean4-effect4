"""Check direct consumers and independent finite controls against the frozen overlay."""
from pathlib import Path
import json
import os
import subprocess
import sys
review = Path(__file__).resolve().parent
root = review.parents[2]
overlay = root / '.lake/host-coalgebra-review-overlay'
logs = review / 'checks'
items = [
    ('controls', review / 'HostControls.lean'),
    ('axioms', review / 'AxiomControls.lean'),
    ('loop-agreement', root / 'src/Effect4/Laws/Program/LoopAgreement.lean'),
    ('runtime', root / 'src/Effect4/Laws/Program/RuntimeR.lean'),
    ('meaning-eq', root / 'src/Effect4/Laws/Program/MeaningEq.lean'),
    ('meaning-sound', root / 'src/Effect4/Laws/Program/MeaningSound.lean'),
    ('agreement-contract', root / 'Test/Program/AgreementContract.lean'),
    ('queue-workload', root / 'Test/Program/QueueWorkload.lean'),
    ('session-meaning', root / 'Test/Api/SessionMeaning.lean'),
    ('checked-instance-control', root / 'docs/research/2026-10-09-host-coalgebra-review/InstanceProbe.lean'),
]
results=[]
for name, source in items:
    cmd=['lake','env','bash','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"',
         'review',str(overlay),'-DwarningAsError=true',str(source)]
    print('CHECK '+name,flush=True)
    run=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'3'},
                       stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(name+'.log')).write_text(run.stdout)
    results.append({'name':name,'command':cmd,'exit_code':run.returncode})
    (logs/'check-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('RESULT '+str(run.returncode),flush=True)
    if run.stdout:
        print(run.stdout,flush=True)
    if run.returncode:
        sys.exit(run.returncode)
print('PASS: narrow consumers, selected laws, and finite controls',flush=True)
