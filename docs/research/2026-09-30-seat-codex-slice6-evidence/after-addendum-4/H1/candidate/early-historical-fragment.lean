/-! The exact early-queue and dispatcher falsifiers, under the retired statements.
Their initialization assumptions are discharged by the budget-80 sleep green. -/
namespace EarlyStep

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- Every command the loop runs from `m` on `cmds` within `fuel` satisfies `ok` (a halted
machine runs nothing). A boolean replay of `driveState` (`Machine/Fibers.lean:1971-1980`). -/
def runsOnly (program : NativeEff) (ok : RCmd → Bool) : Nat → RState → List RCmd → Bool
  | 0, _, _ => true
  | _ + 1, _, [] => true
  | fuel + 1, m, c :: rest =>
    m.stuck.isSome ||
      (ok c && (letI := termEvaluatorFor program
        runsOnly program ok fuel (driveStep (interpR program) m c rest).1
          (driveStep (interpR program) m c rest).2))

/-- The per-command obligations of the commands a run uses, lifted over the command loop (the
seat's `m6_driveState`, restated because probe files cannot import each other, and narrowed to
the commands actually run). -/
theorem drive_of_steps_on (root : ProgramSource) (rootTy : EffTy) (ok : RCmd → Bool)
    (steps : ∀ cmd, ok cmd = true → H1.ReviewedStepPreserves root rootTy cmd) :
    ∀ (fuel : Nat) (w : Typed.World) (m : RState) (cmds : List RCmd),
      H1.ReviewedTypedState root rootTy w m → H1.ReviewedQueueOk root w cmds → runsOnly root.program ok fuel m cmds = true →
      ∃ w', H1.ReviewedTypedState root rootTy w'
        (letI := termEvaluatorFor root.program
         driveState (interpR root.program) fuel m cmds).1 := by
  letI := termEvaluatorFor root.program
  intro fuel
  induction fuel with
  | zero =>
    intro w m cmds ht _ _
    exact ⟨w, by rw [driveState_zero]; exact ht⟩
  | succ fuel ih =>
    intro w m cmds ht hq hr
    cases cmds with
    | nil => exact ⟨w, by rw [driveState_nil]; exact ht⟩
    | cons c rest =>
      rw [driveState_succ_cons]
      by_cases hs : m.stuck.isSome = true
      · rw [if_pos hs]
        exact ⟨w, ht⟩
      · rw [if_neg hs]
        have hr' : m.stuck.isSome = true ∨
            (ok c = true ∧ runsOnly root.program ok fuel (driveStep (interpR root.program) m c rest).1
              (driveStep (interpR root.program) m c rest).2 = true) := by
          simpa only [runsOnly, Bool.or_eq_true, Bool.and_eq_true] using hr
        rcases hr' with hstuck | ⟨hc, hrest⟩
        · exact absurd hstuck hs
        · obtain ⟨w₁, _, ht₁, hq₁⟩ := steps c hc w m rest ht hq
          exact ih w₁ _ _ ht₁ hq₁ hrest

def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def m0 : RState := loadR sleeper 80 80
/-- The code an answer `success 42` becomes (`interpR`'s `answerCode`). -/
def badCode : RProgram := (interpR sleeper).answerCode (.ofExit (.success (.nat 42)))
/-- A resume queued before its token exists. -/
def early : List RCmd := [Cmd.evaluate Api.root, Cmd.resume Api.root 0 badCode, Cmd.drainDue]
def mEnd : RState :=
  (letI := termEvaluatorFor sleeper
   driveState (interpR sleeper) 80 m0 early).1

/-- The five commands the early queue runs. -/
def five : RCmd → Bool
  | .evaluate _ | .loop _ _ | .resume _ _ _ | .finish _ _ | .drainDue => true
  | _ => false

-- Finite checks: no token is allocated at load; after two commands the root is parked at
-- token 0 (allocated by the park); the queued resume then delivers `badCode`; the root exits
-- with 42; the run uses only the five commands.
#guard m0.nextToken == 0
#guard ((letI := termEvaluatorFor sleeper
  driveState (interpR sleeper) 2 m0 early).1.fiber? Api.root).any
    (fun f => f.parked == .withGuard 0)
#guard ((mEnd.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))
#guard runsOnly sleeper five 80 m0 early

theorem early_runsOnly_five : runsOnly sleeper five 80 m0 early = true := by decide

theorem mEnd_bad_exit : ∃ f ∈ mEnd.fibers, f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by
  decide

/-- No world types the end machine (the seat's `bad_not_typed` argument, at this machine). -/
theorem mEnd_not_typed (w : Typed.World) :
    ¬ H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mEnd := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := mEnd_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → FitsExit w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact hs

/-- The early queue is typed in every world that types the loaded machine: the world can declare
no token below `nextToken = 0` (`WorldValid.tokenBound`), so `ResumeOk` is vacuous. -/
theorem early_queueOk (w : Typed.World)
    (h : H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    H1.ReviewedQueueOk (sleeper : ProgramSource) w early := by
  intro c hc
  simp only [early, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · trivial
  · show Contracts.ResumeOk (TypedProg (sleeper : ProgramSource)) w Api.root 0 badCode
    intro ty hty
    exact absurd (h.1.tokenBound _ _ _ hty) (Nat.not_lt_zero 0)
  · trivial

/-- `typedState_load`'s statement at this program and budget. -/
def LoadAt : Prop :=
  Api.typeOf sleeper [] = some (EffTy.pure .unit) → ClosedEff (EffTy.pure .unit) →
    ∃ w, H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 80 80)

/-- **`typedState_load` at `sleeper` and five of the ledger's per-command obligations cannot all
hold.** -/
theorem load_and_five_inconsistent (load : LoadAt)
    (evaluate : ∀ id, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.evaluate id))
    (loop : ∀ id y, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.loop id y))
    (resume : ∀ id t c, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.resume id t c))
    (finish : ∀ id ex, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.finish id ex))
    (drainDue : H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) .drainDue) : False := by
  obtain ⟨w₀, h₀⟩ := load (by rfl') ⟨rfl, rfl⟩
  have steps : ∀ cmd, five cmd = true →
      H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) cmd := by
    intro cmd hc
    cases cmd with
    | evaluate id => exact evaluate id
    | loop id y => exact loop id y
    | resume id t c => exact resume id t c
    | finish id ex => exact finish id ex
    | drainDue => exact drainDue
    | deliver => cases hc
    | launch => cases hc
    | enrollRace => cases hc
    | registrationDone => cases hc
    | interruptTarget => cases hc
    | afterInterrupt => cases hc
    | raceCancel => cases hc
    | trackChild => cases hc
    | observe => cases hc
    | exitDone => cases hc
    | closeParAwait => cases hc
    | link => cases hc
    | wake => cases hc
  obtain ⟨w, hw⟩ := drive_of_steps_on _ _ five steps 80 w₀ m0 early h₀ (early_queueOk w₀ h₀)
    early_runsOnly_five
  exact mEnd_not_typed w hw

/-- The same with all 18, as `m6_capstone_of_steps` and `m6_decision_preserves` take them. -/
theorem load_and_steps_inconsistent (load : LoadAt)
    (steps : ∀ cmd, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) cmd) : False :=
  load_and_five_inconsistent load (fun _ => steps _) (fun _ _ => steps _)
    (fun _ _ _ => steps _) (fun _ _ => steps _) (steps _)

theorem loaded_at80 : LoadAt := by
  intro _ _
  obtain ⟨w, typed⟩ := H1.loaded_sleep80_typed
  exact ⟨w, H1.forget_new_state _ _ _ _ typed⟩

/-- The exact retained early queue makes the old collection of step laws false,
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
end EarlyStep

namespace EarlyDecision

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
    ¬ H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mFired := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := mFired_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → FitsExit w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact hs

/-- The crafted dispatcher is typed in every world that types the loaded machine: its start task
imposes nothing, and its resume's token is undeclared there (`WorldValid.tokenBound`, `nextToken
= 0`). -/
theorem dT_ok (w : Typed.World)
    (h : H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    DispatcherOk (H1.reviewedPreds (sleeper : ProgramSource)) w Expect.root dT := by
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

/-- The retired typed-state predicate admits the crafted machine at the loaded world. -/
theorem mT_typed (w : Typed.World)
    (h : H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mT := by
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
    ∃ w, H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 80 80)

/-- `decision_preserves`'s statement at this program, budget and decision. -/
def FireAt : Prop :=
  ∀ w m, H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m →
    AnswerOk w m (.fire Api.root) →
    ∃ w', w.leHost w' ∧ H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w'
      (letI := termEvaluatorFor sleeper
       stepDecisionState (interpR sleeper) 80 m (.fire Api.root)).1

/-- **`typedState_load` at `sleeper` and `decision_preserves` at `fire root` cannot both hold.**
`fire` is not an answer, so this also makes the premises of the seat's `m6_capstone` (load, and
`decision_preserves` for every non-answer decision) inconsistent at this program. -/
theorem load_and_fire_inconsistent (load : LoadAt) (dec : FireAt) : False := by
  obtain ⟨w₀, h₀⟩ := load (by rfl') ⟨rfl, rfl⟩
  obtain ⟨w, _, hw⟩ := dec w₀ mT (mT_typed w₀ h₀) trivial
  exact mFired_not_typed w hw

theorem loaded_at80 : LoadAt := by
  intro _ _
  obtain ⟨w, typed⟩ := H1.loaded_sleep80_typed
  exact ⟨w, H1.forget_new_state _ _ _ _ typed⟩

/-- The exact retained dispatcher witness refutes the old fire statement,
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
end EarlyDecision
