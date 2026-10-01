#!/usr/bin/env python3
"""Render G candidates under /tmp only. No apply mode and no build commands.
Authorized patch and PROPOSED fourth-fixture patch are separate. Register patch is deferred.
"""
from pathlib import Path
import argparse, difflib, hashlib, json, subprocess
p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,default=Path('/Users/pooks/Dev/lean4-effect4-slice6'))
p.add_argument('--out',type=Path,default=Path('/private/tmp/g-candidate/rendered'))
a=p.parse_args()
assert str(a.out.resolve()).startswith('/private/tmp/'), 'Output must stay under /private/tmp'
new={}; old={}
def get(path):
    old[path]=(a.root/path).read_text()
    new[path]=old[path]
    return old[path]
def replace(path,before,after):
    if path not in old: get(path)
    assert new[path].count(before)==1, f'{path}: exact old block count {new[path].count(before)}'
    new[path]=new[path].replace(before,after)
def patch(before,after):
    result=[]
    for path in sorted(after):
        b=before.get(path,''); n=after[path]
        if b==n: continue
        result.append(f'diff --git a/{path} b/{path}\n')
        if path not in before: result.append('new file mode 100644\n')
        result.extend(difflib.unified_diff(b.splitlines(True),n.splitlines(True),fromfile='a/'+path if path in before else '/dev/null',tofile='b/'+path))
    return ''.join(result)
checker='src/Effect4/Program/Checker.lean'
replace(checker,'''    | .succeed key value => do
      let _ ← expect ⟨p, .literalOutsideAlphabet value⟩ (litVal value)
      pure ⟨Requirement.single key, .never, Requirement.empty⟩
    | .effect key body => do
      let t ← check sig [] (p ++ [0]) body
      pure ⟨Requirement.single key, t.error, bodyRequires sig t⟩
''','''    | .succeed key value => do
      let _ ← expect ⟨p, .literalOutsideAlphabet value⟩ (litVal value)
      let ty ← expect ⟨p, .serviceUnknown key⟩ (sig.serviceTy key)
      if Ty.sub (Lit.ty value).normalize ty.normalize then
        pure ⟨Requirement.single key, .never, Requirement.empty⟩
      else throw ⟨p, .valueNotSubtype key (Lit.ty value) ty⟩
    | .effect key body => do
      let t ← check sig [] (p ++ [0]) body
      let ty ← expect ⟨p, .serviceUnknown key⟩ (sig.serviceTy key)
      if Ty.sub t.answer.normalize ty.normalize then
        pure ⟨Requirement.single key, t.error, bodyRequires sig t⟩
      else throw ⟨p, .valueNotSubtype key t.answer ty⟩
''')
has='src/Effect4/Laws/Program/Typing/HasTy.lean'
replace(has,'''  The premise is that the literal is in the machine's value alphabet — a string is not
  (`PROV-FB-STRING-VALUE`) — and the value's *type* plays no part. -/
  | succeed {key : ServiceKey} {value : Lit} {v : _root_.Effect4.Machine.Env.Val} :
      litVal value = some v →
''','''  The literal is in the machine's value alphabet — a string is not
  (`PROV-FB-STRING-VALUE`) — and its type is below the key's declared service type. -/
  | succeed {key : ServiceKey} {value : Lit} {v : _root_.Effect4.Machine.Env.Val} {ty : Ty} :
      litVal value = some v →
      sig.serviceTy key = some ty →
      Ty.sub (Lit.ty value).normalize ty.normalize = true →
''')
replace(has,'''  `Scope` requirement (`:1438`, `bodyRequires`). -/
  | effect {key : ServiceKey} {body : Eff Op} {t : EffTy} :
      HasTy sig [] body t →
''','''  `Scope` requirement (`:1438`, `bodyRequires`). Its answer is below the key's service type. -/
  | effect {key : ServiceKey} {body : Eff Op} {t : EffTy} {ty : Ty} :
      HasTy sig [] body t →
      sig.serviceTy key = some ty →
      Ty.sub t.answer.normalize ty.normalize = true →
''')
inv='src/Effect4/Laws/Program/Typing/CheckInversion.lean'
replace(inv,'''      ∃ v, litVal value = some v ∧
        l = ⟨Requirement.single key, .never, Requirement.empty⟩ := by
''','''      ∃ v ty, litVal value = some v ∧ sig.serviceTy key = some ty ∧
        Ty.sub (Lit.ty value).normalize ty.normalize = true ∧
        l = ⟨Requirement.single key, .never, Requirement.empty⟩ := by
''')
replace(inv,'''      ∃ t, check sig [] (p ++ [0]) body = .ok t ∧
        l = ⟨Requirement.single key, t.error, bodyRequires sig t⟩ := by
''','''      ∃ t ty, check sig [] (p ++ [0]) body = .ok t ∧ sig.serviceTy key = some ty ∧
        Ty.sub t.answer.normalize ty.normalize = true ∧
        l = ⟨Requirement.single key, t.error, bodyRequires sig t⟩ := by
''')
sound='src/Effect4/Laws/Program/Typing/CheckSound.lean'
replace(sound,'''    obtain ⟨v, hv, rfl⟩ := inv_layer_succeed sig p key value s h
    exact .succeed hv
''','''    obtain ⟨_, _, hv, hkey, hsub, rfl⟩ := inv_layer_succeed sig p key value s h
    exact .succeed hv hkey hsub
''')
replace(sound,'''    obtain ⟨t, ht, rfl⟩ := inv_layer_effect sig p key body s h
    exact .effect (check_sound sig body [] _ t ht)
''','''    obtain ⟨t, _, ht, hkey, hsub, rfl⟩ := inv_layer_effect sig p key body s h
    exact .effect (check_sound sig body [] _ t ht) hkey hsub
''')
provision='src/Effect4/Program/Provision.lean'
replace(provision,'''* **`build`, the specification of provisioning**, structural over the combinators with the
  leaves supplied as a `LeafSem` hook (the trusted-boundary position `ServiceUniverse` and
  `RunInterp` already occupy), and `build_total`: *a well-typed layer builds under every
  context that satisfies its requirement row, and what it builds satisfies its output row*.
  That sentence is what "the `R` channel guarantees the wiring" means, and it is proved once
  over the algebra, for every leaf semantics that is honest about its own leaves.
''','''* **`build`, the specification of provisioning**, structural over the combinators with the
  leaves supplied as a `LeafSem` hook (the trusted-boundary position `ServiceUniverse` and
  `RunInterp` already occupy). The proved laws concern the requirement and context algebra,
  including when a layer signature closes an application's requirements. The connection from
  a well-typed layer to its built context is checked by the finite witnesses below.
''')
replace(provision,'''def leftWins : LayerTerm DocsOp := .merge (.succeed dbKey (.nat 1)) (.succeed dbKey (.nat 2))
def rightWins : LayerTerm DocsOp := .merge (.succeed dbKey (.nat 2)) (.succeed dbKey (.nat 1))

#guard layerTy docsSig leftWins = layerTy docsSig rightWins
#guard (docsLayer leftWins).map buildServices = some [(10, 2), (3, 0)]
#guard (docsLayer rightWins).map buildServices = some [(10, 1), (3, 0)]
#guard (build docsSem leftWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 2))
#guard (build docsSem rightWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 1))
''','''def leftWins : LayerTerm DocsOp := .merge (.succeed dbBinding (.nat 1)) (.succeed dbBinding (.nat 2))
def rightWins : LayerTerm DocsOp := .merge (.succeed dbBinding (.nat 2)) (.succeed dbBinding (.nat 1))

#guard (layerTy docsSig leftWins).isSome
#guard (layerTy docsSig rightWins).isSome
#guard layerTy docsSig leftWins = layerTy docsSig rightWins
#guard (docsLayer leftWins).map buildServices = some [(20, 2), (3, 0)]
#guard (docsLayer rightWins).map buildServices = some [(20, 1), (3, 0)]
#guard (build docsSem leftWins Context.empty).map (fun c => c.getV dbBinding) = some (some (.nat 2))
#guard (build docsSem rightWins Context.empty).map (fun c => c.getV dbBinding) = some (some (.nat 1))
''')
contract='Test/Program/ProvisionContract.lean'
replace(contract,'''-- `E4-PROV-CE-002`, the typing half: one signature.
#guard layerTy docsSig leftWins = layerTy docsSig rightWins

-- `E4-PROV-CE-002`, the run half: two contexts, through the specification and the machine.
#guard (build docsSem leftWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 2))
#guard (build docsSem rightWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 1))
#guard (docsLayer leftWins).map buildServices = some [(10, 2), (3, 0)]
#guard (docsLayer rightWins).map buildServices = some [(10, 1), (3, 0)]
''','''-- `E4-PROV-CE-002`, the typing half: two admitted layers with one signature.
#guard (layerTy docsSig leftWins).isSome
#guard (layerTy docsSig rightWins).isSome
#guard layerTy docsSig leftWins = layerTy docsSig rightWins

-- `E4-PROV-CE-002`, the run half: two contexts, through the specification and the machine.
#guard (build docsSem leftWins Context.empty).map (fun c => c.getV dbBinding) = some (some (.nat 2))
#guard (build docsSem rightWins Context.empty).map (fun c => c.getV dbBinding) = some (some (.nat 1))
#guard (docsLayer leftWins).map buildServices = some [(20, 2), (3, 0)]
#guard (docsLayer rightWins).map buildServices = some [(20, 1), (3, 0)]
''')
author='Test/Program/AuthorContract.lean'
replace(author,'''#guard (Effect4.Api.checkLayer (Layer.value Counter.key (str "x"))).toOption.map
    (fun l => l.provides) = some [Counter.key]
''','''#guard (Effect4.Api.checkLayer (Layer.value Counter.key (str "x"))).map
    (fun _ => ()) = .error (.typing ⟨[], .valueNotSubtype Counter.key .string .nat⟩)
''')
allpath='Test/All.lean'
replace(allpath,'import Test.Counterexamples.Machine.Semantics.M6Capstone\n','import Test.Counterexamples.Machine.Semantics.M6Capstone\nimport Test.Counterexamples.Machine.Semantics.LayerValue\n')
fixture='Test/Counterexamples/Machine/Semantics/LayerValue.lean'
assert not (a.root/fixture).exists(), 'Candidate already applied; do not duplicate it'
new[fixture]=(Path(__file__).parent/'LayerValue.lean').read_text()
# Separate proposal depends on the authorized candidate, not the unmodified repository.
fourth=Path('/private/tmp/GFourthFixtureControls.proposed.lean').read_text()
fragment=fourth[fourth.index('namespace Test.Counterexamples.LayerValue.TemplateFixture'):]
proposed={fixture:new[fixture].replace('import Effect4.Api\n','import Effect4.Api\nimport Test.Codegen.TemplatesContract\n',1)+'\n'+fragment}
a.out.mkdir(parents=True,exist_ok=True)
for path,s in old.items():
    dest=a.out/'baseline'/path; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_text(s)
for path,s in new.items():
    dest=a.out/'authorized'/path; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_text(s)
for path,s in proposed.items():
    dest=a.out/'PROPOSED-fourth'/path; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_text(s)
(a.out/'authorized-source.patch').write_text(patch(old,new))
(a.out/'PROPOSED-fourth-fixture.patch').write_text(patch({fixture:new[fixture]},proposed))
# Explicit, deferred register changes. No other row is touched and F's concurrent row survives.
reg='Test/Counterexamples/REGISTER.md'; reg_old=(a.root/reg).read_text(); reg_new=reg_old
rows=reg_old.splitlines()
ce2=next(x for x in rows if x.startswith('| `E4-PROV-CE-002` |'))
ce6=next(x for x in rows if x.startswith('| `E4-PROV-CE-006` |'))
new2=ce2.replace('(`leftWins`, `rightWins` share a `layerTy`)','(`leftWins`, `rightWins` at number-typed `dbBinding` both check and share a `layerTy`)').replace('`(10, 2)` and `(10, 1)`','`(20, 2)` and `(20, 1)`')
assert new2!=ce2
new6='| `E4-PROV-CE-006` | REPAIRED 2026-10-01 | A layer value fits its key\'s service type | `Test/Counterexamples/Machine/Semantics/LayerValue.lean`: retained old leaf rules, `valueLeak`, `succeedLeak`, `crash2`, unknown-key refusals and matching-value control | Layer leaves require a declared service carrier and normalized value subtyping; the checker and LayerHasTy rules agree. The original gap programs are refused at their layer paths. The authorized Provision and AuthorContract fixtures were updated; finite corpus verdict changes, if any, are recorded in the slice6 receipt. |'
reg_new=reg_new.replace(ce2,new2).replace(ce6,new6)
(a.out/'register-after-success.patch').write_text(patch({reg:reg_old},{reg:reg_new}))
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
manifest={'base_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=a.root,text=True).strip(),'status':'UNCOMPILED candidate; fourth fixture proposal NOT authorized','files':[{'path':path,'before_sha256':sha(old[path]) if path in old else None,'after_sha256':sha(s)} for path,s in sorted(new.items())],'fourth_files':[fixture],'register_deferred_rows':['E4-PROV-CE-002','E4-PROV-CE-006'],'generated_included':[],'preserved_inputs':{path:sha((a.root/path).read_text()) for path in ['src/Effect4/Program/Compile.lean','src/Effect4/Machine/Fibers.lean','ocaml/gen/roots.json','ocaml/engine/externs.txt','ocaml/engine/tools/api_engine_prelude.ml']}}
(a.out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Rendered {len(new)} authorized source/test paths; separate proposed fourth fixture; deferred two-row register patch. No repository writes.')
