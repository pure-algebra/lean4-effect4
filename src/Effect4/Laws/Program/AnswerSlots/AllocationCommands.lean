import Effect4.Laws.Program.AnswerSlots.AllocationAdministration
import Effect4.Laws.Machine.AnswerFlowGhostCommands

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared bare-prefix coupled command/history producer for Atomic and Queue.
Fixed-world commands reuse the existing command theorem.
Actual pending replies read the matching parked suffix; native evaluation remains the advancing attachment.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual fixed-world pending commands retain live reply classes and childless terminal authority. -/
def AdministrativeReady (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) : Cmd EffName EffThunk Val Err Defect FiberId Ann → Prop
  | .loop _ _ | .deliver _ _ | .launch _ | .registrationDone _ _
    | .afterInterrupt _ _ _ | .closeParAwait _ _ _ => False
  | .resume id token code => SourceScope.TerminalReply code ∧ NoRaceReply code ∧
      ∀ fiber, machine.fiber? id = some fiber → fiber.parked = .withGuard token →
        PendingWaits spec fragment ⟨fiber.id, machine.state, false⟩ fiber
  | .finish id _ => ∀ fiber, machine.fiber? id = some fiber → fiber.children = []
  | _ => True

/-- The existing command driver preserves exact pending frames under actual local administrative permissions. -/
theorem administrative_commands (spec : Spec) (fragment : SourceScope.Fragment spec.root) :
    letI := evaluatorFor spec.root spec.table
    AnswerFlow.Commands (interpOf spec.root spec.table) (AdministrativeReady spec fragment)
      (fun world _ => PendingFrame spec fragment world) (fun state id => ⟨id, state, false⟩) := by
  letI := evaluatorFor spec.root spec.table
  refine {
    iteration := ?_, deliver := ?_, interruption := ?_, resume := ?_,
    entrant := ?_, settleRace := ?_, parkRace := ?_, afterInterrupt := ?_, closePar := ?_,
    exitChildren := ?_, publish := ?_, cleared := ?_, link := ?_, drop := ?_, due := ?_, wake := ?_ }
  · intro machine fiber yielding permission held found
    exact permission.elim
  · intro machine fiber yielding permission held found
    exact permission.elim
  · intro state cause fiber held
    exact ⟨FrameAt.interruption spec fragment _ fiber cause held.1, held.2⟩
  · intro machine id token code fiber permission held found parked
    have previous := held.found found
    obtain ⟨output, input, actual, saved⟩ := PendingWaits.resume spec fragment _ fiber code
      (permission.2.2 fiber found parked) (by rw [parked]; intro impossible; cases impossible)
      permission.1 permission.2.1
    exact ⟨⟨input, output, actual, saved⟩, previous.2⟩
  · intro machine raceId race program more host permission held found programs hostFound
    exact permission.elim
  · intro machine raceId yielding race fiber exit permission held found fiberFound accepted
    exact permission.elim
  · intro machine raceId yielding race fiber permission held found fiberFound
    exact permission.elim
  · intro machine host yielding kind fiber permission held found
    exact permission.elim
  · intro machine host yielding fibers fiber permission held found
    exact permission.elim
  · intro machine id exit fiber permission held found runs
    have empty := permission fiber found
    rw [empty] at runs
    simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true] at runs
  · intro state fiber held
    exact ⟨FrameAt.fields spec fragment _ _ _ held.1 rfl rfl, held.2⟩
  · intro state fiber held
    exact ⟨FrameAt.cleared spec fragment _ _ held.1, held.2⟩
  · intro machine mode scope target state key actual fiber member held
    have shape := (pending_store_hooks spec.root spec.table machine.state.refs machine.state.deferreds.cells.length).link
      mode scope target machine.state state key ⟨rfl, rfl⟩ actual
    exact FrameAt.store_fields spec fragment fiber.id machine.state state fiber.frame held shape.1 shape.2
  · intro machine scope key state actual fiber member held
    have shape := (pending_store_hooks spec.root spec.table machine.state.refs machine.state.deferreds.cells.length).drop
      scope key machine.state state ⟨rfl, rfl⟩ actual
    exact FrameAt.store_fields spec fragment fiber.id machine.state state fiber.frame held shape.1 shape.2
  · intro machine fiber member held
    have shape := (pending_store_hooks spec.root spec.table machine.state.refs machine.state.deferreds.cells.length).due
      machine.state ⟨rfl, rfl⟩
    exact FrameAt.store_fields spec fragment fiber.id machine.state _ fiber.frame held shape.1 shape.2
  · intro machine list phase fiber member held
    have shape := (pending_store_hooks spec.root spec.table machine.state.refs machine.state.deferreds.cells.length).wake
      list phase machine.state ⟨rfl, rfl⟩
    exact FrameAt.store_fields spec fragment fiber.id machine.state _ fiber.frame held shape.1 shape.2
end Effect4.Program.AnswerSlots.AllocationAdapter
