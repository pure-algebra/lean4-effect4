"""Check direct consumers and independent finite controls against the frozen overlay."""
from pathlib import Path
import json
import os
import subprocess
import sys
review = Path(__file__).resolve().parent
root = review.parents[2]
overlay = root / '.lake/host-coalgebra-review-overlay'
logs = review / 'checks/h9'
logs.mkdir(parents=True, exist_ok=True)
items = [
    ('h9-reader', review / 'H9Controls.lean'),
    ('h9-axioms', review / 'H9AxiomControls.lean'),
    ('h9-session-meaning', root / 'Test/Api/SessionMeaning.lean'),
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
