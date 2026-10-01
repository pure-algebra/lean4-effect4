from pathlib import Path
import difflib,hashlib,json,re,subprocess
root=Path('/Users/pooks/Dev/lean4-effect4-slice6')
base=root/'docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/H1/candidate'
out=Path('/private/tmp/h1-addendum6')
paths=['src/Effect4/Laws/Program/Guard/Core.lean','src/Effect4/Laws/Program/Guard/RegistrationQueue.lean','src/Effect4/Laws/Program/Typed/Scheduler.lean','src/Effect4/Laws/Program/Typed/Assembly.lean']
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
manifest={'status':'uncompiled draft; preserve before probing queue discard','source_root':str(root),'source_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'authority':'addendum 6 ea5b28b5; row 133','files':{},'standalone_probes':{}}
patch=[]
for p in paths:
 before=(root/p).read_text() if (root/p).exists() else ''; earlier=(base/p).read_text();after=(out/p).read_text()
 patch.extend(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p if before else '/dev/null',tofile='b/'+p))
 blocks=[]
 for b in difflib.SequenceMatcher(None,earlier.splitlines(),after.splitlines(),autojunk=False).get_matching_blocks():
  if b.size:blocks.append({'candidate_start':b.b+1,'preserved_start':b.a+1,'lines':b.size})
 declarations=[{'kind':m.group(1),'name':m.group(2),'line':after[:m.start()].count('\n')+1} for m in re.finditer(r'^(def|theorem|structure) ([^\s(:]+)',after,re.M)]
 manifest['files'][p]={'live_before_sha256':sha(before),'preserved_candidate_sha256':sha(earlier),'candidate_sha256':sha(after),'preserved_candidate':str(base/p),'matching_line_blocks':blocks,'declarations':declarations}
(out/'source.patch').write_text(''.join(patch))
for name in ['TerminalPositive.lean','QueueDiscardWitness.lean']:
 s=(out/name).read_text();manifest['standalone_probes'][name]={'sha256':sha(s),'theorems':re.findall(r'^theorem ([^\s(:]+)',s,re.M),'axiom_prints':re.findall(r'^#print axioms (.+)$',s,re.M)}
(out/'source-map.json').write_text(json.dumps(manifest,indent=2)+'\n')
axioms=(base/'Axioms.lean').read_text()
(out/'Axioms.lean').write_text(axioms+'\n#print axioms Effect4.Program.Typed.savedPosition_of_saved\n')
print('Prepared source.patch, source-map.json and axiom appendix; no repository writes, Lean or git apply.')
