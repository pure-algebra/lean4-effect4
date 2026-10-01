#!/usr/bin/env python3
"""Copy two existing test helper statements/bodies unchanged except namespace qualification."""
from pathlib import Path
import hashlib,json,re
repo=Path('/Users/pooks/Dev/lean4-effect4-slice6')
base=Path('/private/tmp/h2-part-one-repaired/probes')
out=Path('/private/tmp/h2-part-one-controls')
lines=(base/'Repaired.lean').read_text().splitlines()
mapping=json.loads((base/'Repaired.map.json').read_text())
mapping['probe']='ExistingTestsFirstPass'
ns='Research.Slice6.H2ExistingTestControls'
lines.extend(['',f'namespace {ns}',
'open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote',
'open Effect4.Program.Typed Effect4.Laws.Effects',
'abbrev W := Effect4.Program.Typed.World',
'def sleeping : NativeEff := .perform .sleep (.lit (.nat 1))',
'def sleepCancel : EffName := .withWaiter (.store .cancelSleep) Api.root 0',
'def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩',
'def readService : NativeEff := .service natKey',
'theorem natKey_ty : nativeServiceTy natKey = some .nat := by decide +kernel',
'theorem fitsExit_unit (w : W) : FitsExit w (EffTy.pure .unit) (.success .unit) := trivial',''])
for filename,name,originalns in [
 ('Test/Program/TypedControl.lean','cancel_typed','Test.Program.TypedControl'),
 ('Test/Program/LoadedAdmission.lean','lookup_typed','Test.Program.LoadedAdmission')]:
    path=repo/filename;text=path.read_text();src=text.splitlines()
    start=next(i for i,s in enumerate(src) if s.startswith('theorem '+name+' '))
    end=next((i for i in range(start+1,len(src)) if re.match(r'^(?:theorem|def|/--|/-!)',src[i])),len(src))
    hstart=len(lines)+1
    for i in range(start,end):
        s=re.sub(r'\bTypedProg\b','Research.Slice6.H2Repaired.TypedProg',src[i])
        lines.append(s)
        mapping['line_map'].append({'harness_line':len(lines),'module':'ExistingTest','source_line':i+1,'input_path':str(path)})
    mapping['declarations'].append({'kind':'theorem','original_declaration':originalns+'.'+name,
        'harness_declaration':ns+'.'+name,'module':'ExistingTest','source_module':filename,
        'input_path':str(path),'source_start':start+1,'source_end':end,
        'harness_start':hstart,'harness_end':len(lines)})
    lines.append('')
lines.append('end '+ns)
result='\n'.join(lines)+'\n';mapping['harness_sha256']=hashlib.sha256(result.encode()).hexdigest()
mapping['note']='Existing test statements and proof bodies copied literally, except fully qualifying TypedProg to the requested repaired judgment. Neither test signature has been amended.'
(out/'ExistingTestsFirstPass.lean').write_text(result)
(out/'ExistingTestsFirstPass.map.json').write_text(json.dumps(mapping,indent=2)+'\n')
print('Wrote ExistingTestsFirstPass.lean and source map; no Lean invoked.')
