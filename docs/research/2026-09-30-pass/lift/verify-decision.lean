import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Program.Typed.Assembly

/-!
# Research.Pass.LiftVerify.Decision — the ledger's `decision_preserves` fails at `fire`

`TypedState` (`Typed/Assembly.lean:67-72`) types a dispatcher's resume task through `ResumeOk`
(`TaskOk`, generated; `preds.ResumeOk`, `:55`), which is vacuous when the world does not declare
the task's token (`Typed/Contracts.lean:74-75`). So a machine whose dispatcher holds a resume for
a token that no park has allocated yet is typed whenever the machine without that task is.

The probe: take the loaded `sleeper` machine and give the root's dispatcher two tasks, `start
root` and `resume root 0 bad`. If the loaded machine is typed in a world (`typedState_load`), the
new one is typed in the same world (`mT_typed`). The `fire root` decision runs the start task,
which parks the root at token 0 (allocating it), then the resume task, which delivers `bad`: the
root exits with `success 42` at a `unit` type. So `typedState_load` at this program and
`decision_preserves` at `fire` cannot both hold.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Pass.LiftVerify.Decision

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def m0 : RState := loadR sleeper 80 80
def badCode : RProgram := (interpR sleeper).answerCode (.ofExit (.success (.nat 42)))

/-- A dispatcher with a start task and a resume for token 0, which no park has allocated. -/
def dT : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram :=
  ⟨[⟨0, [.start Api.root, .resume Api.root 0 badCode]⟩], true⟩

/-- The loaded machine with that dispatcher on its fiber. Not reachable; typed all the same. -/
def mT : RState := { m0 with fibers := m0.fibers.map (fun f => { f with dispatcher := dT }) }

def mFired : RState :=
  (letI := termEvaluatorFor sleeper
   stepDecisionState (interpR sleeper) 80 mT (.fire Api.root)).1

-- Finite checks: the fire runs both tasks and the root exits with 42.
#guard (dT.drain.1.length == 2)
#guard ((mFired.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))

theorem mFired_bad_exit :
    ∃ f ∈ mFired.fibers, f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by
  decide

theorem mFired_not_typed (w : Typed.World) :
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mFired := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := mFired_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → StrongExit w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact Bool.noConfusion hs.1

/-- The crafted dispatcher is typed in every world that types the loaded machine: its start task
imposes nothing, and its resume's token is undeclared there (`WorldValid.tokenBound`, `nextToken
= 0`). -/
theorem dT_ok (w : Typed.World)
    (h : TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    DispatcherOk (preds (sleeper : ProgramSource)) w Expect.root dT := by
  refine ⟨fun b hb => ⟨fun t ht => ?_⟩⟩
  change b ∈ [⟨0, [.start Api.root, .resume Api.root 0 badCode]⟩] at hb
  rw [List.mem_singleton] at hb
  subst hb
  change t ∈ [.start Api.root, .resume Api.root 0 badCode] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · trivial
  · show Contracts.ResumeOk (TypedProg (sleeper : ProgramSource)) w Api.root 0 badCode
    intro ty hty
    exact absurd (h.1.tokenBound _ _ _ hty) (Nat.not_lt_zero 0)

/-- **`TypedState` admits the crafted machine**: typed in the loaded machine's world. -/
theorem mT_typed (w : Typed.World)
    (h : TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mT := by
  have hd := dT_ok w h
  obtain ⟨hv, hok, hpark⟩ := h
  refine ⟨⟨hv.ids, hv.fibers, hv.heap, hv.promises, ?_, hv.tokenBound, hv.tokenTargets, hv.state,
    hv.wf, hv.cells, hv.fiberClosed, hv.heapClosed, hv.promiseClosed, hv.tokenClosed, hv.root⟩,
    ⟨?_, hok.c1, hok.c2⟩, ?_⟩
  · intro f hf token hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hv.tokens g hg token hp
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    have old := hok.c0 g hg
    exact ⟨old.c0, old.c1, old.c2, old.c3, hd, old.c5⟩
  · intro f hf token hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hpark g hg token hp

/-- `typedState_load`'s statement at this program and budget. -/
def LoadAt : Prop :=
  Api.typeOf sleeper [] = some (EffTy.pure .unit) → ClosedEff (EffTy.pure .unit) →
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 80 80)

example : ProofGraph.Obligation LoadAt :=
  M3bAssembly.typedState_load (sleeper : ProgramSource) (EffTy.pure .unit) 80 80

/-- `decision_preserves`'s statement at this program, budget and decision. -/
def FireAt : Prop :=
  ∀ w m, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m →
    AnswerOk w m (.fire Api.root) →
    ∃ w', w.leHost w' ∧ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w'
      (letI := termEvaluatorFor sleeper
       stepDecisionState (interpR sleeper) 80 m (.fire Api.root)).1

example : ProofGraph.Obligation FireAt :=
  M6Ledger.decision_preserves (sleeper : ProgramSource) (EffTy.pure .unit) 80 (.fire Api.root)

/-- **`typedState_load` at `sleeper` and `decision_preserves` at `fire root` cannot both hold.**
`fire` is not an answer, so this also makes the premises of the seat's `m6_capstone` (load, and
`decision_preserves` for every non-answer decision) inconsistent at this program. -/
theorem load_and_fire_inconsistent (load : LoadAt) (dec : FireAt) : False := by
  obtain ⟨w₀, h₀⟩ := load (by rfl') ⟨rfl, rfl⟩
  obtain ⟨w, _, hw⟩ := dec w₀ mT (mT_typed w₀ h₀) trivial
  exact mFired_not_typed w hw

end Research.Pass.LiftVerify.Decision

#print axioms Research.Pass.LiftVerify.Decision.mFired_bad_exit
#print axioms Research.Pass.LiftVerify.Decision.mFired_not_typed
#print axioms Research.Pass.LiftVerify.Decision.dT_ok
#print axioms Research.Pass.LiftVerify.Decision.mT_typed
#print axioms Research.Pass.LiftVerify.Decision.load_and_fire_inconsistent
