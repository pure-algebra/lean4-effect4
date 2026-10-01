from pathlib import Path
import re
ROOT=Path('/Users/pooks/Dev/lean4-effect4-slice6')
SRC=ROOT/'docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/H1/TerminalSavedWitness.candidate.lean'
OUT=Path('/private/tmp/h1-addendum6')
s=SRC.read_text()
# Preserve all fifteen checked theorem bodies against their exact old state and step propositions.
s=s.replace('namespace H1TerminalSavedWitness','namespace H1TerminalAmendment').replace('end H1TerminalSavedWitness','end H1TerminalAmendment').replace('H1TerminalSavedWitness.','H1TerminalAmendment.')
s=s.replace('TypedState','OldTypedState').replace('StepPreserves','OldStepPreserves')
s=s.replace('No altered or historical state judgment here.','The former state and step judgments are retained below as historical definitions.')
s=s.replace('No runtime or contract change is proposed in this file.','The new positive controls use production TypedState with its exact pending queue.')
anchor='abbrev W := Effect4.Program.Typed.World\n'
block='''
/-- The checked pre-row-133 H1 state; intentionally independent of the amended current-code clause. -/
def OldTypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

def OldStepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, OldTypedState root rootTy w m → QueueOk root w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ OldTypedState root rootTy w' r.1 ∧ QueueOk root w' r.1 r.2
'''
s=s.replace(anchor,anchor+block,1)
# Extract checked complete theorem declarations without their comments/next declarations.
def block_of(name):
 text=SRC.read_text(); start=text.index('theorem '+name+' ')
 end=re.search(r'^((?:theorem|def|#|end)\b|/--)',text[start+1:],re.M)
 return text[start:start+1+end.start()].rstrip()+'\n' if end else text[start:]
new=[]
base=block_of('typed')
base=base.replace('theorem typed : TypedState','theorem typed_queued (commands : List RCmd) : TypedState').replace('world machine := by','world machine commands := by')
base=base.replace('      exact saved_typed','      exact savedPosition_of_saved _ _ _ _ _ _ _ saved_typed')
new.append(base)
for name in ['valid','no_requests','scheduler','observers','registration']:
 b=block_of(name)
 b=re.sub(r'\bmachine\b','result.1',b)
 b=re.sub(r'\bfiber\b','afterFiber',b)
 b=b.replace('theorem '+name,'theorem result_'+name,1)
 if name=='scheduler': b=re.sub(r'\bno_requests\b','result_no_requests',b)
 new.append(b)
b=block_of('typed')
b=b.replace('theorem typed : TypedState','theorem result_typed : TypedState').replace('world machine := by','world result.1 result.2 := by')
b=re.sub(r'\bmachine\b','result.1',b);b=re.sub(r'\bfiber\b','afterFiber',b)
for name in ['valid','scheduler','observers','registration']:b=re.sub(r'\b'+name+r'\b','result_'+name,b)
b=b.replace('      exact saved_typed','''      refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
      intro live
      apply False.elim
      apply live
      exact Or.inl ⟨.success .unit, by
        rw [result_commands]
        exact List.mem_singleton_self _⟩''')
new.append(b)
new.append('''theorem result_queue : QueueOk (rootProgram : ProgramSource) world result.1 result.2 := by
  rw [result_commands]
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ⟨trivial, trivial⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    intro ty declared
    rw [result_valid.root] at declared
    cases declared
    trivial
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    exact ⟨afterFiber, result_fiber, rfl, rfl⟩
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    trivial
  · intro key member; cases member
  · intro id token request lookup
    rw [result_no_requests] at lookup
    cases lookup
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member
  · intro race child member
    rw [List.mem_singleton] at member
    cases member
  · intro host yielding race member
    rw [List.mem_singleton] at member
    cases member

/-- The actual changing-intermediate-type input and the output of its delivery are both
accepted; this finite positive does not assert any of the eighteen general transition laws. -/
theorem deliver_preserves_this_state :
    TypedState (rootProgram : ProgramSource) unitTy world machine [command] ∧
    QueueOk (rootProgram : ProgramSource) world machine [command] ∧
    ∃ w', world.leHost w' ∧
      TypedState (rootProgram : ProgramSource) unitTy w' result.1 result.2 ∧
      QueueOk (rootProgram : ProgramSource) w' result.1 result.2 :=
  ⟨typed_queued [command], queue, world, leHost_refl world, result_typed, result_queue⟩

/-- Consuming finish publishes the same exit while the old code remains in its inert slot. -/
def completed : RState × List RCmd :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) result.1 (.finish Api.root (.success .unit)) []

theorem completed_commands : completed.2 = [.drainDue] := rfl

def publishedFiber : RFiber :=
  { afterFiber with exit := some (.success .unit), running := false }

theorem completed_fiber : completed.1.fiber? Api.root = some publishedFiber := rfl

theorem completed_position : TerminalPosition completed.1 completed.2 (.fiber Api.root) :=
  Or.inr ⟨publishedFiber, List.mem_of_find?_eq_some completed_fiber, rfl, rfl⟩

theorem published_saved_typed : SavedPosition (rootProgram : ProgramSource) world completed.1
    completed.2 (.fiber Api.root) unitTy publishedFiber.frame :=
  ⟨unitTy, (fun live => False.elim (live completed_position)), .nil _,
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
''')
append='\n/-! Row 133: normal terminal delivery and published-code boundary. Uncompiled draft. -/\n\n'+'\n'.join(new)+'\n'
names=re.findall(r'^theorem ([A-Za-z0-9_]+)',append,re.M)
append+='\n'.join('#print axioms '+n for n in names)+'\n'
append=append.replace('.afterFiber?', '.fiber?')
s=s.replace('\nend H1TerminalAmendment',append+'\nend H1TerminalAmendment',1)
(OUT/'TerminalPositive.lean').write_text(s)
print('Wrote TerminalPositive.lean with',len(names),'new theorem drafts and fifteen retained checked bodies.')
