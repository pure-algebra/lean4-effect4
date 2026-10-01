#!/usr/bin/env python3
"""Compose standalone candidate controls below /private/tmp; no repository writes or Lean."""
from pathlib import Path
import hashlib,json,re
base=Path('/private/tmp/h2-part-one-candidate')
repaired=Path('/private/tmp/h2-part-one-repaired')
out=Path('/private/tmp/h2-part-one-controls')
repo=Path('/Users/pooks/Dev/lean4-effect4-slice6')
# Append controls to an exact namespaced copy of the repaired declarations.
controls=(out/'Controls.lean').read_text()
controls=controls.replace('import Effect4.Laws.Program.Typed.Assembly\n','',1)
# Resolve every candidate-owned name explicitly, so the imported old module cannot
# accidentally discharge an assertion against the pre-H2 judgment.
names=['ExitOk','NoShapeDefect','TypedProg','ProgramSource','strongExit_of_clean']
for name in names:
    controls=re.sub(r'\b'+re.escape(name)+r'\b','Research.Slice6.H2Repaired.'+name,controls)
(out/'RepairedControls.lean').write_text((repaired/'probes/Repaired.lean').read_text()+'\n'+controls)
# Freeze all four pre-H2 modules for the historic field-only failure. The original
# side-audit used pre-E StrongExit; the retained E baseline supplies unchanged FitsExit.
original=repo/'docs/research/2026-09-30-side-audit/probes/BadDefectCurrent.lean'
red=original.read_text()
red='\n'.join(s for s in red.splitlines() if not s.startswith('import '))+'\n'
red=red.replace('StrongExit','FitsExit')
for name in ['ProgramSource','TypedProg','preds','frameProtocols','strongExit_of_clean']:
    red=re.sub(r'\b'+name+r'\b','Research.Slice6.H2Baseline.'+name,red)
red=red.replace('namespace SideAudit.BadDefectCurrent','namespace Research.Slice6.H2FieldOnlyRed')
red=red.replace('end SideAudit.BadDefectCurrent','end Research.Slice6.H2FieldOnlyRed')
header='import Effect4.Laws.Program.Guard.Core\n'
# Import directives must precede the copied declaration bodies.
baseline=(base/'probes/Baseline.lean').read_text()
red=header+baseline+'\n'+red
(out/'FieldOnlyRed.lean').write_text(red)
manifest={'repaired_harness_sha256':hashlib.sha256((repaired/'probes/Repaired.lean').read_bytes()).hexdigest(),
'baseline_harness_sha256':hashlib.sha256((base/'probes/Baseline.lean').read_bytes()).hexdigest(),
'historical_probe_path':str(original),'historical_probe_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
'field_only_changes':['imports hoisted','namespace renamed','StrongExit -> unchanged FitsExit (E baseline)',
'candidate-owned baseline names fully qualified'],'lean_run':False,
'note':'The original full badDefect clause is frozen locally only in field-only historical control. Production part one ignores missingService.'}
(out/'controls-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Wrote RepairedControls.lean and FieldOnlyRed.lean; no Lean invoked.')
