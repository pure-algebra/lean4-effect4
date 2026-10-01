#!/usr/bin/env python3
from pathlib import Path
import re
base=Path('/private/tmp/h2-part-one-controls')
for stem in ('LookupDiagnostic','CancelDiagnostic'):
    s=(base/(stem+'.fragment.lean')).read_text()
    for name in ['ProgramSource','TypedProg','ExitOk','strongExit_success','unguard_payload_inv']:
        s=re.sub(r'\b'+name+r'\b','Research.Slice6.H2Repaired.'+name,s)
    (base/(stem+'.lean')).write_text((base/'RepairedControls.lean').read_text()+s)
print('Wrote both standalone diagnostic candidates; no Lean invoked.')
