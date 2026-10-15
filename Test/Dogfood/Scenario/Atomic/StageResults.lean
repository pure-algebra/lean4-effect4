import Test.Dogfood.Scenario.Atomic.StageQueue

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the active Atomic native command and settlement postcondition.
The checked local actor results supply actual live roles and completion-command exits.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Actual root native results retain the live role consumed by disposition. -/
theorem OutcomeRole.root (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (result : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (identity : result.fiber.id = ⟨0⟩) (running : result.fiber.running = true)
    (held : External.Native.ResultAt (RootGraph.model root table view) (RootGraph.Edge root table)
      world .ordinary result) : OutcomeRole root table world result := by
  unfold OutcomeRole
  cases outcome : result.outcome
  all_goals simp only [External.Native.ResultAt, outcome] at held
  case finished exit => exact running
  all_goals exact .root identity held

/-- Actual daemon native results retain their live role before every nonterminal disposition. -/
theorem OutcomeRole.daemon (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (result : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (identity : result.fiber.id = ⟨1⟩) (running : result.fiber.running = true)
    (held : DaemonGraph.FrameAt root table world result.fiber.frame) : OutcomeRole root table world result := by
  unfold OutcomeRole
  cases result.outcome
  case finished exit => exact running
  all_goals exact .daemon identity held

/-- Actual request native results retain their live role or remain running until publication. -/
theorem OutcomeRole.request (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (owner : Nat) (member : owner ∈ requests)
    (result : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (identity : result.fiber.id = ⟨owner + 1⟩) (running : result.fiber.running = true)
    (held : External.Native.ResultAt (StageGraph.model root table owner view) (StageGraph.Edge root table owner)
      world (.finalized owner) result) : OutcomeRole root table world result := by
  unfold OutcomeRole
  cases outcome : result.outcome
  all_goals simp only [External.Native.ResultAt, outcome] at held
  case finished exit => exact running
  all_goals exact .request owner member identity held

/-- The root's actual completion never publishes a request's exit. -/
theorem CompletedAt.root (world : StageWorld.World) (exit : ExitV) : CompletedAt world ⟨0⟩ exit := by
  intro owner member identity
  have same : 0 = owner + 1 := congrArg FiberId.value identity
  have impossible : False := by omega
  exact impossible.elim

/-- The daemon's actual completion never publishes a request's exit. -/
theorem CompletedAt.daemon (world : StageWorld.World) (exit : ExitV) : CompletedAt world ⟨1⟩ exit := by
  intro owner member identity
  have same : 1 = owner + 1 := congrArg FiberId.value identity
  have zero : owner = 0 := by omega
  subst owner
  exact False.elim ((by decide : (0 : Nat) ∉ requests) member)

/-- An actual request completion supplies exactly the exit permission consumed by its finish command. -/
theorem CompletedAt.request (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (owner : Nat) (exit : ExitV)
    (held : ExitAt (StageGraph.model root table owner view) world (.finalized owner) exit) :
    CompletedAt world ⟨owner + 1⟩ exit := by
  intro selected member identity
  have same : owner + 1 = selected + 1 := congrArg FiberId.value identity
  have equal : owner = selected := Nat.add_right_cancel same
  subst selected
  cases exit <;> exact held

end Test.Dogfood.Scenario.Atomic.StageConfiguration
