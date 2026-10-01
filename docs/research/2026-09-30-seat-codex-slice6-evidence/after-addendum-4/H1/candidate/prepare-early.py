from pathlib import Path
root=Path('/Users/pooks/Dev/lean4-effect4-slice6')
out=Path('/private/tmp/h1-candidate')
# Add the exact budget-80 green used by both retained early-resume falsifiers.
p=out/'tests-fragment.lean'
s=p.read_text()
a=s.index('-- This local builder')
b=s.index('theorem loaded_typed :',a)
block=s[a:b]
block=block.replace('theorem typed_loaded (p : NativeEff) (resultTy : EffTy) (closed : ClosedEff resultTy)',
 'theorem typed_loaded_at (p : NativeEff) (resultTy : EffTy) (fuel compileFuel : Nat)\n    (closed : ClosedEff resultTy)')
block=block.replace('(rootPoint 20)', '(rootPoint compileFuel)')
block=block.replace('(loadR p 20 20)', '(loadR p fuel compileFuel)')
block=block.replace('initial_world_valid _ p 20 20', 'initial_world_valid _ p fuel compileFuel')
block=block.replace('schedulerState_load p 20 20', 'schedulerState_load p fuel compileFuel')
block=block.replace('observerState_load (p : ProgramSource) _ 20 20', 'observerState_load (p : ProgramSource) _ fuel compileFuel')
block+='''theorem typed_loaded (p : NativeEff) (resultTy : EffTy) (closed : ClosedEff resultTy)
    (code : ∀ w, TypedProg (p : ProgramSource) w resultTy (denoteR p p (rootPoint 20))) :
    ∃ w, TypedState (p : ProgramSource) resultTy w (loadR p 20 20) :=
  typed_loaded_at p resultTy 20 20 closed code

'''
s=s[:a]+block+s[b:]
a=s.index('theorem loaded_sleep_code (')
b=s.index('/-- Freeze the pre-H1',a)
extra=s[a:b].replace('loaded_sleep_code','loaded_sleep80_code').replace('loaded_sleep_typed','loaded_sleep80_typed')
extra=extra.replace('rootPoint 20','rootPoint 80').replace('loadR sleeper 20 20','loadR sleeper 80 80')
extra=extra.replace('typed_loaded sleeper (EffTy.pure .unit)', 'typed_loaded_at sleeper (EffTy.pure .unit) 80 80')
s=s[:b]+extra+s[b:]
s=s.replace('#print axioms loaded_sleep_typed', '#print axioms loaded_sleep_typed\n#print axioms loaded_sleep80_typed')
p.write_text(s)

# Keep the accepted finite machine witnesses and conditional proofs, but freeze pre-H1
# predicates locally and discharge their old initialization premise using the new green.
fragments=[]
for filename,oldns,newns in [
 ('verify-steppreserves.lean','Research.Pass.LiftVerify','EarlyStep'),
 ('verify-decision.lean','Research.Pass.LiftVerify.Decision','EarlyDecision')]:
 s=(root/'docs/research/2026-09-30-pass/lift'/filename).read_text()
 a=s.index('namespace '+oldns)
 b=s.index('end '+oldns,a)
 s=s[a:b]
 s=s.replace('namespace '+oldns,'namespace '+newns,1)
 s=s.replace('StepPreserves ', 'H1.ReviewedStepPreserves ')
 s=s.replace('TypedState ', 'H1.ReviewedTypedState ')
 s=s.replace('QueueOk ', 'H1.ReviewedQueueOk ')
 s=s.replace('(preds ', '(H1.reviewedPreds ')
 s=s.replace('StrongExit ', 'FitsExit ')
 s=s.replace('exact Bool.noConfusion hs.1', 'exact hs')
 # Historical proof obligations differ from new ones, so do not reuse the new wrappers.
 while 'example : ProofGraph.Obligation ' in s:
  a=s.index('example : ProofGraph.Obligation ')
  b=s.index('\n\n',a)
  s=s[:a]+s[b+2:]
 s+='''theorem loaded_at80 : LoadAt := by
  intro _ _
  obtain ⟨w, typed⟩ := H1.loaded_sleep80_typed
  exact ⟨w, H1.forget_new_state _ _ _ _ typed⟩

'''
 if newns=='EarlyStep':
  s+='''/-- The exact retained early queue makes the old collection of step laws false,
now without assuming initialization. This proves no repaired transition law. -/
theorem old_steps_false :
    ¬ (∀ command, H1.ReviewedStepPreserves (sleeper : ProgramSource)
      (EffTy.pure .unit) command) := by
  intro steps
  exact load_and_steps_inconsistent loaded_at80 steps

/-- The repaired fact refuses the exact early queue before execution. -/
theorem early_queue_rejected (w : Typed.World) :
    ¬ QueueOk (sleeper : ProgramSource) w m0 early := by
  intro queue
  have impossible : 0 < 0 := queue.keys.below (Api.root, 0) (List.mem_singleton_self _)
  exact Nat.not_lt_zero 0 impossible

#print axioms old_steps_false
#print axioms early_queue_rejected
'''
 else:
  s+='''/-- The exact retained dispatcher witness refutes the old fire statement,
now without assuming initialization. -/
theorem old_fire_false : ¬ FireAt := by
  intro fire
  exact load_and_fire_inconsistent loaded_at80 fire

/-- The new state rejects the exact stored early resume through the shared key list. -/
theorem early_dispatcher_rejected (w : Typed.World) :
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mT := by
  intro typed
  have impossible : 0 < 0 := typed.2.2.2.1.keysBelow (Api.root, 0)
    (List.mem_singleton_self _)
  exact Nat.not_lt_zero 0 impossible

#print axioms old_fire_false
#print axioms early_dispatcher_rejected
'''
 s+='end '+newns+'\n'
 fragments.append(s)
(out/'early-historical-fragment.lean').write_text('''/-! The exact early-queue and dispatcher falsifiers, under the retired statements.
Their initialization assumptions are discharged by the budget-80 sleep green. -/\n'''+ '\n'.join(fragments))

p=out/'prepare.py'
s=p.read_text()
needle="s = (root / rel).read_text()\ns = replace_once(s, 'end Test.Counterexamples.Machine.Semantics.M6Capstone',"
repl="s = (root / rel).read_text()\ns = replace_once(s, 'import Effect4.Laws.Program.Typed.Assembly\\n', 'import Effect4.Laws.Program.Typed.Assembly\\nimport Effect4.Laws.Machine.Approximation\\n')\ns = replace_once(s, 'end Test.Counterexamples.Machine.Semantics.M6Capstone',"
assert s.count(needle)==1
s=s.replace(needle,repl)
needle="(out / 'observe-historical-fragment.lean').read_text() + '\\nend Test.Counterexamples.Machine.Semantics.M6Capstone')"
repl="(out / 'observe-historical-fragment.lean').read_text() + '\\n' + (out / 'early-historical-fragment.lean').read_text() + '\\nend Test.Counterexamples.Machine.Semantics.M6Capstone')"
assert s.count(needle)==1
p.write_text(s.replace(needle,repl))
