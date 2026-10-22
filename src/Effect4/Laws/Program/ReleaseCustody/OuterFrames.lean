import Effect4.Laws.Program.ReleaseCustody.NativeMachineShape
import Effect4.Laws.Program.ReleaseCustody.CommandSequencing
import Effect4.Laws.Machine.Lift

/-!
Concept: scope-lifetime-finalization, R11.
Question: saved-frame sequencing at outer edits serves Execution.history through Machine.Lift.
Reach: actual dispatcher drain, scheduler verdict, interruption, clock drain and answer preparation.
Limit: these transports establish no command ownership, source multiplicity, custody funding or progress.
Unlock: the joint history assertion retains ConfigurationKept outside the command runner.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.OuterFrames
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.RuntimeShape

/-- A keyed metadata edit retains saved frames when its changed fiber does.
Consumer: scheduler verdict and dispatcher updates. -/
theorem modify (m : NativeMachine) (id : FiberId) (edit : Control.Fiber → Control.Fiber)
    (held : ConfigurationKept m) (kept : ∀ fiber ∈ m.fibers, FiberKept (edit fiber)) :
    ConfigurationKept (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i fiber found
    exact CommandSequencing.configuration_update m (edit fiber) held
      (kept fiber (List.mem_of_find?_eq_some found))

/-- Draining the actual dispatcher changes none of its owner's saved frames.
Consumer: Machine.Lift's drain clause in the custody history proof. -/
theorem drain (m : NativeMachine) (owner : FiberId) (fiber : Control.Fiber)
    (held : ConfigurationKept m) (found : m.fiber? owner = some fiber) :
    ConfigurationKept ((m.update {fiber with dispatcher := fiber.dispatcher.drain.2}).disarm owner) := by
  exact CommandSequencing.configuration_update m _ held
    (CommandSequencing.fiber_fields fiber _ (held fiber (List.mem_of_find?_eq_some found)) rfl rfl rfl)

/-- A scheduler verdict changes none of the selected fiber's saved frames.
Consumer: Machine.Lift's yield clause in the custody history proof. -/
theorem yield (m : NativeMachine) (id : FiberId) (verdict : Bool) (held : ConfigurationKept m) :
    ConfigurationKept (m.modify id fun fiber => {fiber with yieldOverride := some verdict}) := by
  apply modify m id _ held
  intro fiber member
  exact CommandSequencing.fiber_fields fiber _ (held fiber member) rfl rfl rfl

/-- The actual outer interrupt is one classified other-fiber edit plus its trace events.
Consumer: Machine.Lift's interruption clause in the custody history proof. -/
theorem interrupt (interp : Moves.NInterp) (m : NativeMachine) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (target : FiberId) (fiber : Control.Fiber)
    (held : ConfigurationKept m) (found : m.fiber? target = some fiber) :
    ConfigurationKept (Lift.interruptEdit interp m who extra target fiber) := by
  have changed := CommandSequencing.configuration_update m (interruptRecord interp who extra fiber).1 held
    (NativeMachineShape.edit (.interrupted interp fiber who extra)
      (held fiber (List.mem_of_find?_eq_some found)))
  unfold Lift.interruptEdit
  dsimp only
  split <;> exact changed

/-- Posting a task changes only dispatcher metadata of an existing owner.
Consumer: the clock's actual owed-resume drain. -/
theorem post (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : Task EffName EffThunk Val Err Defect FiberId Ann) (held : ConfigurationKept m) :
    ConfigurationKept (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact held
  · rename_i fiber found
    exact CommandSequencing.configuration_update m _ held
      (CommandSequencing.fiber_fields fiber _ (held fiber (List.mem_of_find?_eq_some found)) rfl rfl rfl)

/-- Both immediate and scheduled owed resumes retain saved frames before their commands run.
Consumer: Machine.Lift's clock clause in the custody history proof. -/
theorem drain_owed (m : NativeMachine) (owed : List (Owed NCode)) (held : ConfigurationKept m) :
    ConfigurationKept (drainOwed m owed).1 := by
  induction owed generalizing m with
  | nil => exact held
  | cons next rest ih =>
    simp only [drainOwed]
    split
    · exact ih m held
    · exact ih _ (post m _ _ _ held)

/-- Clock advancement edits the store before draining its actual owed resumes.
Consumer: Machine.Lift's clock clause, without a restriction on wake modes. -/
theorem clock (root : NativeEff) (table : RowTable) (m : NativeMachine) (millis : ClockMillis)
    (held : ConfigurationKept m) :
    ConfigurationKept (drainOwed
      {m with state := ((interpOf root table).clockStep millis m.state).2}
      ((interpOf root table).clockStep millis m.state).1.toList).1 :=
  drain_owed _ _ held

/-- Reply preparation edits the external store before its first resume command.
Consumer: Machine.Lift's answer clause in the custody history proof. -/
theorem prepare (root : NativeEff) (table : RowTable) (m : NativeMachine) (id : FiberId)
    (token : Nat) (answer : Completion Val Err Defect FiberId Ann) (held : ConfigurationKept m) :
    ConfigurationKept {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1} :=
  held
end Effect4.Program.ReleaseCustody.OuterFrames
