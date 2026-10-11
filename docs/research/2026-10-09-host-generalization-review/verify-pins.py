"""Verify the landing and unchanged public obligations from retained bytes."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

review=Path(__file__).resolve().parent
root=review.parents[2]
base='0a108d2f91dce4a0f8a2fa7899228e2541ccf8ea'
landed='feb968d7fdbce63089cd40ff5f467d6e2bd3de58'
pins=json.loads((review/'input-pins.json').read_text())
checks=[]
for path, expected in pins['files'].items():
    captured=(review/'snapshot'/path).read_bytes()
    committed=subprocess.check_output(['git','show',landed+':'+path],cwd=root)
    actual=hashlib.sha256(committed).hexdigest()
    assert actual==expected and captured==committed,path
    checks.append({'path':path,'sha256':actual,'identical_to_landing':True})

def public_text(source,name,definition=False):
    kind='def' if definition else 'theorem'
    start=re.search(r'^'+kind+r' '+name+r'\b',source,re.M).start()
    text=source[start:]
    if definition:
        text=text.split('\n\n',1)[0]
    else:
        text=text.split(':=',1)[0]
    return ' '.join(text.split())

signatures=[]
for name,path,definition in [
    ('DenoteRowsEqSession','src/Effect4/Laws/Api/SessionMeaning.lean',True),
    ('denoteRows_eq_session','src/Effect4/Laws/Api/SessionMeaning.lean',False),
    ('replay_Mexit_of_localRun','src/Effect4/Laws/Program/Agreement/Segment.lean',False),
    ('replay_Mexit','src/Effect4/Laws/Program/Agreement/Segment.lean',False),
    ('run_eq_meaning','src/Effect4/Laws/Program/Agreement/Segment.lean',False),
]:
    before=subprocess.check_output(['git','show',base+':'+path],cwd=root,text=True)
    after=(review/'snapshot'/path).read_text()
    old=public_text(before,name,definition)
    new=public_text(after,name,definition)
    assert old==new,name
    signatures.append({'declaration':name,'path':path,'normalized_statement':new,'unchanged':True})
record={'base':base,'landing':landed,'files':checks,'public_statements':signatures}
(review/'landing-match.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: five files match landing; five public statements match the previous reviewed commit.')
