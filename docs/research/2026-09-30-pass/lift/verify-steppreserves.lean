import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Program.Typed.Assembly

/-!
# Research.Pass.LiftVerify.StepPreserves — the ledger's per-command obligations are inconsistent

Adversarial check of the LIFT seat's M6 instance. `StepPreserves` (`Typed/Assembly.lean:93-97`)
quantifies over every pending list `rest`, and `QueueOk` types a queued `resume` only when the
world already declares its token (`ResumeOk`, `Typed/Contracts.lean:74-75`). A resume queued for
a token that is not yet allocated is therefore typed vacuously. The next park allocates that
token (`Machine/Fibers.lean:1078-1080`), and the resume then delivers whatever code it carries.

The probe: from the loaded `sleeper` machine, the queue `[evaluate root, resume root 0 bad,
drainDue]` is `QueueOk` in every world that types the machine (no token is declared there, since
`nextToken = 0`), and the command loop runs the root to the exit `success 42` at a `unit` type.
So `typedState_load` at this program and five of the 18 per-command obligations (`evaluate`,
`loop`, `resume`, `finish`, `drainDue`) cannot all hold.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Pass.LiftVerify

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
    (steps : ∀ cmd, ok cmd = true → StepPreserves root rootTy cmd) :
    ∀ (fuel : Nat) (w : Typed.World) (m : RState) (cmds : List RCmd),
      TypedState root rootTy w m → QueueOk root w cmds → runsOnly root.program ok fuel m cmds = true →
      ∃ w', TypedState root rootTy w'
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
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mEnd := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := mEnd_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → StrongExit w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact Bool.noConfusion hs.1

/-- The early queue is typed in every world that types the loaded machine: the world can declare
no token below `nextToken = 0` (`WorldValid.tokenBound`), so `ResumeOk` is vacuous. -/
theorem early_queueOk (w : Typed.World)
    (h : TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    QueueOk (sleeper : ProgramSource) w early := by
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
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 80 80)

/-- The ledger's obligation is this statement (checked by the kernel). -/
example : ProofGraph.Obligation LoadAt :=
  M3bAssembly.typedState_load (sleeper : ProgramSource) (EffTy.pure .unit) 80 80

/-- **`typedState_load` at `sleeper` and five of the ledger's per-command obligations cannot all
hold.** -/
theorem load_and_five_inconsistent (load : LoadAt)
    (evaluate : ∀ id, StepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.evaluate id))
    (loop : ∀ id y, StepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.loop id y))
    (resume : ∀ id t c, StepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.resume id t c))
    (finish : ∀ id ex, StepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.finish id ex))
    (drainDue : StepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) .drainDue) : False := by
  obtain ⟨w₀, h₀⟩ := load (by rfl') ⟨rfl, rfl⟩
  have steps : ∀ cmd, five cmd = true →
      StepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) cmd := by
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
    (steps : ∀ cmd, StepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) cmd) : False :=
  load_and_five_inconsistent load (fun _ => steps _) (fun _ _ => steps _)
    (fun _ _ _ => steps _) (fun _ _ => steps _) (steps _)

end Research.Pass.LiftVerify

#print axioms Research.Pass.LiftVerify.drive_of_steps_on
#print axioms Research.Pass.LiftVerify.early_runsOnly_five
#print axioms Research.Pass.LiftVerify.mEnd_bad_exit
#print axioms Research.Pass.LiftVerify.mEnd_not_typed
#print axioms Research.Pass.LiftVerify.early_queueOk
#print axioms Research.Pass.LiftVerify.load_and_five_inconsistent
#print axioms Research.Pass.LiftVerify.load_and_steps_inconsistent
