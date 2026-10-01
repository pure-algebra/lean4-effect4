#!/usr/bin/env python3
"""F source/test patch only. Default renders /tmp; --apply writes eight named paths.
Generated ML and closure manifests are excluded byte-for-byte and must be regenerated.
--base-ref is read-only verification against a git ref, never an apply source.
REGISTER repair is emitted as a separate after-success patch and is NEVER applied here.
"""
from pathlib import Path
import argparse, subprocess, re, hashlib, json, difflib
p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,default=Path('/Users/pooks/Dev/lean4-effect4-slice6'))
p.add_argument('--out',type=Path,default=Path('/private/tmp/f-source-candidate'))
p.add_argument('--base-ref')
p.add_argument('--repair-date',default='2026-10-01')
p.add_argument('--apply',action='store_true')
a=p.parse_args()
if a.apply and a.base_ref: raise SystemExit('--base-ref is validation-only; cannot combine with --apply')
if not re.fullmatch(r'\d{4}-\d{2}-\d{2}',a.repair_date): raise SystemExit('Expected YYYY-MM-DD repair date')
evidence=Path('docs/research/2026-09-30-seat-codex-slice6-evidence/F/implementation.patch')
payload=(a.root/evidence).read_bytes()
expected_hash='646bce8ad956bf8b898e85dd22d33a763af33b61cbbcac823ac7babaecdf3715'
assert hashlib.sha256(payload).hexdigest()==expected_hash, 'Original F evidence patch changed; review it before updating this assertion'
allowed={
 'Test/All.lean',
 'Test/Counterexamples/Machine/Runtime/LayerEnvironment.lean',
 'ocaml/engine/test/test_engine.ml',
 'src/Effect4/Program/Compile.lean',
 'src/Effect4/Laws/Program/Agreement.lean',
 'src/Effect4/Laws/Program/DenoteR.lean',
 'src/Effect4/Laws/Program/Handles/Layer.lean',
 'src/Effect4/Laws/Program/Intro/Layer.lean',
}
excluded={
 'ocaml/engine/api_engine.ml',
 'ocaml/gen/api_gen.ml',
 'ocaml/gen/closure-api_engine.tsv',
 'ocaml/gen/closure-api_gen.tsv',
}

def read(path):
 if a.base_ref:
  q=subprocess.run(['git','ls-tree','--name-only',a.base_ref,'--',path],cwd=a.root,text=True,capture_output=True,check=True)
  if not q.stdout.strip(): return None
  return subprocess.run(['git','show',f'{a.base_ref}:{path}'],cwd=a.root,text=True,capture_output=True,check=True).stdout
 f=a.root/path
 return f.read_text() if f.exists() else None

blocks={}
for block in re.split(r'(?m)^diff --git ',payload.decode())[1:]:
 header=block.splitlines()[0]
 m=re.fullmatch(r'a/(.+) b/(.+)',header)
 assert m and m[1]==m[2], f'Unexpected diff path header: {header}'
 path=m[1]
 assert path not in blocks, f'Duplicate file: {path}'
 blocks[path]='diff --git '+block
assert set(blocks)==allowed|excluded, f'Unexpected original patch path set: {set(blocks) ^ (allowed|excluded)}'
old={}; new={}; reports=[]
for path in sorted(allowed):
 original=read(path); old[path]=original
 block=blocks[path]
 if path=='Test/All.lean':
  # A is now landed in both supported states. Preserve A's reserved anchor and all C imports/deletions.
  anchor='import Test.Counterexamples.Machine.Runtime.HostHandleForgery\n'
  added='import Test.Counterexamples.Machine.Runtime.LayerEnvironment\n'
  assert original is not None and original.count(anchor)==1, 'Missing/ambiguous A import anchor'
  assert added not in original, 'F import already exists'
  new[path]=original.replace(anchor,anchor+added)
  reports.append({'path':path,'hunks':1,'adaptation':'Place the F import after the now-landed A HostHandleForgery import, as addendum 2 requires.'})
  continue
 isnew='\n--- /dev/null\n' in block
 assert (original is None)==isnew, f'{path}: new/existing file state disagrees with evidence patch'
 text=original or ''
 hunks=re.split(r'(?m)^@@ ',block)[1:]
 assert hunks, f'{path}: no hunks'
 for index,hunk in enumerate(hunks,1):
  header,body=hunk.split('\n',1)
  hm=re.match(r'-(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',header)
  assert hm, f'{path}: invalid hunk header: {header}'
  before=[]; after=[]
  for line in body.splitlines(keepends=True):
   if line.startswith('\\ No newline at end of file'): raise SystemExit('Unexpected no-newline hunk; review manually')
   assert line and line[0] in ' +- ', f'{path}: invalid patch line: {line!r}'
   if line[0] in ' -': before.append(line[1:])
   if line[0] in ' +': after.append(line[1:])
  assert len(before)==int(hm[2] or '1') and len(after)==int(hm[4] or '1'), f'{path}: hunk line count mismatch'
  before=''.join(before); after=''.join(after)
  if isnew:
   assert len(hunks)==1 and before=='' and text=='', f'{path}: unexpected new-file shape'
   text=after
  else:
   count=text.count(before)
   assert count==1, f'{path} hunk {index}: old context matched {count} times, expected exactly one'
   text=text.replace(before,after)
 new[path]=text
 reports.append({'path':path,'hunks':len(hunks),'adaptation':None})

# Check feature and controls without invoking any build or generator.
compile_path='src/Effect4/Program/Compile.lean'
assert new[compile_path].count('def layerBuild (p : Point) : Point :=')==1
assert 'EffName.withMemoMapThen p.layerBuild scope' in new[compile_path]
assert 'EffName.buildWithScopeFromContext p.layerBuild scope' in new[compile_path]
fixture=new['Test/Counterexamples/Machine/Runtime/LayerEnvironment.lean']
for name in ['errLeak','forkLeak','discardLeak','crash1','bodyRetainsOuter','serviceContextRetained']:
 assert f'def {name}' in fixture, f'Missing F fixture {name}'
engine=new['ocaml/engine/test/test_engine.ml']
assert engine.count('let layer_environment_check () =')==1
assert 'layer environment Fast uses the body binding' in engine
assert 'layer environment Ref uses the body binding' in engine

# Prepare the exact single-row REGISTER change separately. Do not apply before all F checks pass.
register_path='Test/Counterexamples/REGISTER.md'
register=read(register_path)
assert register is not None
row='| `E4-PROV-CE-005` | SEEDED 2026-09-30 | A layer body runs in the environment in which it was checked | `docs/research/2026-09-30-pass/registry/LayerGap.lean`: `errLeak_checked`, `errLeak_native_exit`, `errLeak_reference_exit`; `registry/verify-Gaps.lean`: `discardLeak_native_exit`, `crash1`, `errLeak_admitted` | Checked at (nat,string), errLeak fails with 9 on both machines: the checker closes the body, but construction retains the enclosing environment. Repair dispatched as item F. |'
assert register.count(row)==1, 'CE005 row changed; review status instead of overwriting it'
repaired=f'| `E4-PROV-CE-005` | REPAIRED {a.repair_date} | A layer body runs in the environment in which it was checked | `Test/Counterexamples/Machine/Runtime/LayerEnvironment.lean`: `errLeak`, `forkLeak`, `discardLeak`, `crash1`, `bodyRetainsOuter`, `serviceContextRetained`; `ocaml/engine/test/test_engine.ml`: `layer_environment_check` | `Point.layerBuild` closes the layer build environment on the native and reference machines while retaining the program body environment and service context. The finite repaired runs pass; regenerated OCaml Fast and Ref both return `failure [fail(text x)]` for errLeak. Discovery evidence remains in the registry probes. |'
register_after=register.replace(row,repaired)
register_patch=''.join(difflib.unified_diff(register.splitlines(True),register_after.splitlines(True),fromfile='a/'+register_path,tofile='b/'+register_path))

# No writes occur until every path, hunk and register assertion succeeds.
a.out.mkdir(parents=True,exist_ok=True)
patch=''
manifest=[]
for path in sorted(allowed):
 original=old[path]; text=new[path]
 patch+=''.join(difflib.unified_diff((original or '').splitlines(True),text.splitlines(True),fromfile='/dev/null' if original is None else 'a/'+path,tofile='b/'+path))
 manifest.append({'path':path,'operation':'create' if original is None else 'edit','before_sha256':None if original is None else hashlib.sha256(original.encode()).hexdigest(),'after_sha256':hashlib.sha256(text.encode()).hexdigest()})
for path,text in new.items():
 destination=a.root/path if a.apply else a.out/path
 destination.parent.mkdir(parents=True,exist_ok=True); destination.write_text(text)
(a.out/'source.patch').write_text(patch)
(a.out/'register-after-success.patch').write_text(register_patch)
(a.out/'manifest.json').write_text(json.dumps({'read_base':a.base_ref or 'current tree','original_evidence_sha256':expected_hash,'changes':manifest,'excluded_generated':sorted(excluded),'hunks':reports},indent=2)+'\n')
print('APPLIED' if a.apply else 'RENDERED ONLY',len(new),'source/test paths; generated excluded:',len(excluded))
print(a.out/'source.patch')
print('Deferred REGISTER:',a.out/'register-after-success.patch')
