#!/usr/bin/env python3
"""Proposed H2 test migrations only; no repository writes and no Lean execution.
These existing test-body edits are NOT exempted from the owner's eight-body cap.
Keep compiler attribution first. Two old test-helper signatures are false under ExitOk.
"""
from pathlib import Path
import argparse,difflib,hashlib,json,re
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source',default='/Users/pooks/Dev/lean4-effect4-slice6')
ap.add_argument('--out',default='/private/tmp/h2-test-migrations')
a=ap.parse_args();root=Path(a.source).resolve();out=Path(a.out).resolve()
if not out.is_relative_to(Path('/private/tmp')):raise RuntimeError('output must be under /private/tmp')
files={};notes={}
def read(path):
    s=(root/path).read_text();files[path]=[s,s];return s
def put(path,s,note):files[path][1]=s;notes[path]=note
def once(s,old,new,count=1):
    actual=s.count(old)
    if actual!=count:raise RuntimeError(f'expected{count}, got{actual}: {old[:90]!r}')
    return s.replace(old,new)
def controls_import(s):
    return once(s,s.splitlines()[0]+'\n',s.splitlines()[0]+'\nimport Test.Program.H2PartOne\n')

p='Test/Program/TypedResidual.lean';s=read(p)
s=once(s,'exact forged_cell_not_fit w hnone hstrong','exact forged_cell_not_fit w hnone hstrong.1',2)
put(p,s,'Two existing refusal proofs project base membership from the strengthened inversion result.')

p='Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean';s=read(p)
s=once(s,'have unit : FitsExit w mid (.success .unit) :=','have unit : ExitOk w mid (.success .unit) :=')
s=once(s,'  exact TypedProg.pure_inv (run w (leHost_refl w) (.success .unit) ⟨rfl, unit⟩)',
'  exact (TypedProg.pure_inv (run w (leHost_refl w) (.success .unit) ⟨rfl, unit⟩)).1')
s=once(s,'  exact does_not_fit w (TypedProg.pure_inv (answer (.failure poisonedCause) ex))',
'  exact does_not_fit w (TypedProg.pure_inv (answer (.failure poisonedCause) ex)).1')
put(p,s,'Preserve ReviewedControlAdmitted/ReviewedTypedProg and historical base FitsExit unchanged; adapt only landed inversion consumers in cancellation_exit/sleep_stack_rejected.')

p='Test/Counterexamples/Machine/Semantics/TrivialPosts.lean';s=controls_import(read(p))
s=once(s,'TypedProg.pure (fitsExit_success w\' _ ans hpost)','TypedProg.pure (strongExit_success w\' _ ans hpost)')
s=once(s,'exact TypedProg.pure trivial','exact TypedProg.pure ⟨trivial, trivial⟩')
s=once(s,"| none => exact TypedProg.pure (fitsExit_of_clean w' ty _ rfl)",
"| none => exact TypedProg.pure (Test.Program.H2PartOne.interrupt_admitted w' ty none)")
put(p,s,'joinAll_typed/modify_typed add vacuous success exclusion; joinsFiber_typed supplies finite interrupt exclusion. Pass-through protocol posts now already carry ExitOk.')

p='Test/Program/TypedControl.lean';s=controls_import(read(p))
anchor='/-! ## Positive: the generated sleep cancellation and the reachable stack -/'
helpers='''/-- Test adapters retain the old base membership helpers above. -/
theorem exitOk_unit (w : W) : ExitOk w (EffTy.pure .unit) (.success .unit) :=
  ⟨fitsExit_unit w, trivial⟩

theorem exitOk_nat (w : W) (ty : EffTy) (n : Nat) (answer : ty.answer = .nat) :
    ExitOk w ty (.success (.nat n)) := ⟨fitsExit_nat w ty n answer, trivial⟩

theorem natErr_shape (ty : EffTy) (n : Nat) : NoShapeDefect ty (.failure (natErr n)) := by
  intro reason member
  simp only [natErr, List.mem_singleton] at member
  subst member
  trivial

theorem natErr_exitOk (w : W) (ty : EffTy) (n : Nat) (error : ty.error = .nat) :
    ExitOk w ty (.failure (natErr n)) := ⟨natErr_fits w ty n error, natErr_shape ty n⟩

'''
s=once(s,anchor,helpers+anchor)
s=once(s,'The generated cancellation is typed at `unit`/`never` for every clean cause: the store',
'The generated cancellation is typed at `unit`/`never` for a clean cause with explicit\nshape exclusion. Cleanliness alone admits excluded defects. The store')
s=once(s,'theorem cancel_typed (w : W) (cause : CauseV) (clean : cleanExit (.failure cause) = true) :',
'''theorem cancel_typed (w : W) (cause : CauseV) (clean : cleanExit (.failure cause) = true)
    (shape : NoShapeDefect (EffTy.pure .unit) (.failure cause)) :''')
s=once(s,"TypedProg.unguard (fitsExit_unit w')","TypedProg.unguard (exitOk_unit w')")
s=once(s,"TypedProg.pure (fitsExit_of_clean w' _ cause clean)","TypedProg.pure (strongExit_of_clean w' _ cause clean shape)")
s=once(s,'  cancel_typed w _ rfl','  cancel_typed w _ rfl (Test.Program.H2PartOne.interrupt_admitted w _ (some Api.root)).2')
s=once(s,'Contracts.StackAccepts (TypedProg sleeping) FitsExit','Contracts.StackAccepts (TypedProg sleeping) ExitOk')
s=once(s,'exact cancel_typed w cause (cleanExit_of_never_fits w _ cause rfl typed)',
'exact cancel_typed w cause (cleanExit_of_never_fits w _ cause rfl typed.1) typed.2')
s=once(s,'TypedProg.unguard (natErr_fits w _ 7 rfl)','TypedProg.unguard (natErr_exitOk w _ 7 rfl)')
s=once(s,"TypedProg.pure (fitsExit_nat w'' _ 0 rfl)","TypedProg.pure (exitOk_nat w'' _ 0 rfl)")
s=once(s,'TypedProg.unguard (fitsExit_nat w _ 1 rfl)','TypedProg.unguard (exitOk_nat w _ 1 rfl)')
s=once(s,'exact TypedProg.pure trivial','exact TypedProg.pure ⟨trivial, trivial⟩')
s=once(s,"exact fitsExit_of_clean w' _ c (cleanExit_of_never_fits w' _ c rfl hex)",
"exact strongExit_of_clean w' _ c (cleanExit_of_never_fits w' _ c rfl hex.1) hex.2")
s=once(s,'    (skip w (leHost_refl w) _ inner rfl)','    (skip w (leHost_refl w) _ inner rfl).1')
s=once(s,'fun h => unguard_payload_inv root w _ _ k h','fun h => (unguard_payload_inv root w _ _ k h).1')
put(p,s,'PROPOSED SIGNATURE AMENDMENT: cancel_typed needs explicit NoShapeDefect premise (independent diagnostic provided). Keep old base helper semantics; introduce new test adapters and project base results in refusals.')

p='Test/Program/TypedStack.lean';s=read(p)
s=once(s,'open Test.Program.TypedControl (natErr natErr_fits fitsExit_nat)',
'open Test.Program.TypedControl (natErr natErr_exitOk exitOk_nat)')
s=once(s,'StackAccepts (TypedProg root) FitsExit','StackAccepts (TypedProg root) ExitOk',2)
s=once(s,'fitsExit_nat w _ 0 rfl','exitOk_nat w _ 0 rfl')
s=once(s,'natErr_fits w _ 7 rfl','natErr_exitOk w _ 7 rfl',3)
s=once(s,'(skip (.failure (natErr 7)) (natErr_exitOk w _ 7 rfl) rfl)',
'(skip (.failure (natErr 7)) (natErr_exitOk w _ 7 rfl) rfl).1')
put(p,s,'Use ExitOk stack contract and finite success/Fail adapters; keep wrong-middle counterexample with first projection of skip output.')

p='Test/Counterexamples/Machine/Semantics/ValueMembership.lean';s=read(p)
s=once(s,'exact TypedProg.pure ⟨rfl, .nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩',
'exact TypedProg.pure ⟨⟨rfl, .nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩')
s=once(s,'exact TypedProg.unguard ⟨rfl, .nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩',
'exact TypedProg.unguard ⟨⟨rfl, .nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩')
s=once(s,"have hv : Fits w' v (.handle NativeOp.refTarget) := hpost.2",
"have hv : Fits w' v (.handle NativeOp.refTarget) := hpost.2.1")
s=once(s,"exact TypedProg.pure (fits_sub w''' hsub ans hfit)",
"exact TypedProg.pure ⟨fits_sub w''' hsub ans hfit, trivial⟩")
s=once(s,"exact fitsExit_of_clean w' _ c (cleanExit_of_never_fits w' _ c rfl hex)",
"exact strongExit_of_clean w' _ c (cleanExit_of_never_fits w' _ c rfl hex.1) hex.2")
put(p,s,'Only new production refProg_typedF/getProg_typedF controls migrate. Reviewed, ExactSpelling, ReviewedLoad historical definitions/proofs stay byte-identical.')

p='Test/Counterexamples/Machine/Semantics/M6Capstone.lean';s=read(p)
s=once(s,'''  change ∀ ty, w.Γ f.id = some ty → FitsExit w ty (.success (.nat 42)) at he
  apply bad_exit_not_typed w
  apply he (EffTy.pure .unit)
  rw [hid]
  exact h.1.root''','''  change ∀ ty, w.Γ f.id = some ty → ExitOk w ty (.success (.nat 42)) at he
  apply bad_exit_not_typed w
  exact (he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)).1''')
put(p,s,'Refusal of the forged host answer still uses the identical base membership contradiction, projected from ExitOk.')

# LoadedAdmission carries a separate required premise amendment; keep its entire proposed
# file in a visibly separate tree, never bundled into an automatically applied patch.
p='Test/Program/LoadedAdmission.lean';s=controls_import(read(p))
s=once(s,'exact TypedProg.pure ⟨_, hid, Ty.sub_refl _, Ty.sub_refl _⟩',
'exact TypedProg.pure ⟨⟨_, hid, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩')
start=s.index('/-- The lookup is typed at the key\'s type for every context whose services are typed. -/')
end=s.index('\ntheorem service_admitted ',start)
s=s[:start]+'''/-- Proposed amendment: the input must actually decode as a context; the old implication
was vacuous at malformed values and admitted badName. -/
theorem lookup_typed (w : W) (ty : EffTy) (answer : ty.answer = .nat) (v : Val)
    (isContext : ∃ ctx, Val.context? v = some ctx)
    (typed : ∀ ctx, Val.context? v = some ctx → ServicesFit w ctx.services) :
    TypedProg readService w ty (serviceLookupR natKey v) := by
  obtain ⟨ctx, hctx⟩ := isContext
  unfold serviceLookupR
  rw [hctx]
  split
  · rename_i sv hget
    have hfit := flatFits_fits (typed ctx hctx natKey sv .nat hget natKey_ty)
    refine TypedProg.pure (strongExit_success w ty sv ?_)
    rw [answer]
    exact hfit
  · exact TypedProg.pure (Test.Program.H2PartOne.missingService_admitted_at_any_type w ty)

/-- The existing context fit supplies the finite decoder witness needed by the amended test. -/
theorem context_of_fits (w : W) (v : Val) (typed : Fits w v (.handle Ty.contextTarget)) :
    ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services := by
  simp only [Effect4.Program.Typed.Fits] at typed
  split at typed
  · simp only [HandleFits] at typed
    split at typed
    · exact absurd typed.1 (by decide)
    · exact absurd typed.1 (by decide)
    · exact absurd typed (by decide)
    · exact absurd typed.1 (by decide)
    · exact typed.elim
  · obtain ⟨_, ctx, hctx, services, _⟩ := typed
    exact ⟨ctx, hctx, services⟩
''' + s[end:]
s=once(s,"TypedProg.unguard (fitsExit_success w' _ ans hpost)","TypedProg.unguard (strongExit_success w' _ ans hpost)")
s=once(s,'''      have hv : Fits w' v (.handle Ty.contextTarget) := hpost.2
      apply lookup_typed w' ty answer v
      intro ctx hctx
      simp only [Effect4.Program.Typed.Fits] at hv
      split at hv
      · exact nomatch hctx
      · obtain ⟨_, ctx', hctx', services, _⟩ := hv
        rw [hctx] at hctx'
        cases hctx'
        exact services''','''      obtain ⟨ctx, hctx, services⟩ := context_of_fits w' v hpost.2.1
      apply lookup_typed w' ty answer v ⟨ctx, hctx⟩
      intro ctx' hctx'
      rw [hctx] at hctx'
      cases hctx'
      exact services''')
s=once(s,"exact fitsExit_of_clean w' ty c (cleanExit_of_never_fits w' _ c rfl hex)",
"exact strongExit_of_clean w' ty c (cleanExit_of_never_fits w' _ c rfl hex.1) hex.2")
s=once(s,"exact TypedProg.pure (fitsExit_of_clean w' _ _ rfl)",
"exact TypedProg.pure (Test.Program.H2PartOne.interrupt_admitted w' _ none)")
put(p,s,'PROPOSED SIGNATURE AMENDMENT: lookup_typed requires actual context witness. Old signature has independent counterexample. service_admitted supplies it from its existing Fits premise, via new finite context_of_fits helper.')

controls=Path('/private/tmp/h2-part-one-controls/Controls.lean').read_text()
interrupt='''
theorem interrupt_admitted (w : W) (ty : EffTy) (who : Option FiberId) :
    ExitOk w ty (.failure (Cause.interrupt who)) := by
  apply strongExit_of_clean w ty _ rfl
  apply noShapeDefect_of_interrupts
  intro reason member
  simp only [Cause.interrupt_reasons, List.mem_singleton] at member
  subst member
  rfl

#print axioms interrupt_admitted
'''
controls=once(controls,'end Test.Program.H2PartOne',interrupt+'end Test.Program.H2PartOne')
files['Test/Program/H2PartOne.lean']=['',controls]
notes['Test/Program/H2PartOne.lean']='New control battery only; historical field-only red and exact old-signature refutations remain separate diagnostic artifacts.'
patch=[];manifest={'lean_run':False,'scope':'PROPOSED ONLY. No existing test body is exempted from the strict cap. Fresh compiler attribution comes first.','files':{}}
for path,(old,new) in files.items():
    dest=out/'proposed'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(new)
    manifest['files'][path]={'input_sha256':hashlib.sha256(old.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(new.encode()).hexdigest(),'note':notes[path]}
    patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=('a/'+path if old else '/dev/null'),tofile='b/'+path))
(out/'PROPOSED-test-migrations.patch').write_text(''.join(patch))
(out/'test-migrations-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'proposed_changed_test_files':len(files)-1,'new_controls':1,'repo_writes':0,'lean_run':False},indent=2))
