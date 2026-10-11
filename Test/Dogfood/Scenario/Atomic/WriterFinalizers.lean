import Test.Dogfood.Scenario.Atomic.WriterEvaluation
import Test.Dogfood.Scenario.Atomic.WriterSync
import Effect4.Laws.Machine.WriterWeights

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: actual native finalizer issuance in Atomic.Cleanup.log_debits.
Every dormant source finalizer creates only its matching recorded writer allowance.
The proof consumes the shared native start law and the actual source address census.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterFinalizers
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase WriterSource
local instance : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq
local instance : LawfulBEq (List Nat) := @List.instLawfulBEq Nat _ Nat.instLawfulBEq
local instance : ReflBEq (List Nat) := @List.instReflBEq Nat _ Nat.instLawfulBEq.toReflBEq

/-- Each actual finalizer child has exactly its matching selected note reservation. -/
def entrySite (id : Nat) (path : List Nat) (node : Node NativeOp) : Bool :=
  match node with
  | .eff (.onExit _ _) =>
    WriterPhase.below id (path ++ [1]) == (if path == SourcePaths.requestPath id then 1 else 0)
  | _ => true

theorem entry_census :
    (Store.shopProgram.map fun root => requests.all fun id =>
      (Node.addresses (.eff root)).all fun path => (Node.at_ (.eff root) path).all (entrySite id path)) = some true := by kernel_rfl

/-- The actual onExit constructor reserves only its matching recorded start allowance. -/
theorem entry_at (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (path : List Nat) (owned : ExitAt built.program path) :
    WriterPhase.below id (path ++ [1]) = (if path == SourcePaths.requestPath id then 1 else 0) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have checked := entry_census
  rw [source] at checked
  obtain ⟨body, cleanup, found⟩ := owned
  have present := (mem_addresses_iff (.eff built.program) path).mpr (by rw [found]; rfl)
  have selected := List.all_eq_true.mp (List.all_eq_true.mp (Option.some.inj checked) id member) path present
  rw [found] at selected
  exact beq_iff_eq.mp selected

/-- Every actual finalizer program spends its saved allowance or its matching recorded start. -/
theorem program_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV))
    (callback : EffName) (exit : ExitV) (program : NCode) (owned : NameAt built.program callback)
    (produced : (interpAt built.program view built.table).finalizerProgram callback exit = some program) :
    current id program ≤ name id callback + (if FinalizerRun.atPath (SourcePaths.requestPath id) callback then 1 else 0) := by
  cases callback
  case fin point =>
    cases produced
    have bounded := resolve_bound built admitted id member ({point with completed := view}.childWith 1 (reifyExitVal exit))
      (childWith_at built.program {point with completed := view} 1 (reifyExitVal exit) owned.1)
    have reserved := entry_at built admitted id member point.path owned.2
    change current id (resolve built.program ({point with completed := view}.childWith 1 (reifyExitVal exit))) ≤
      WriterPhase.below id (point.path ++ [1]) at bounded
    rw [reserved] at bounded
    simpa only [name, FinalizerRun.atPath, Nat.zero_add, beq_iff_eq] using bounded
  case store stored =>
    cases stored
    case finalizerName captured =>
      cases produced
      change current id (embed (finProgram captured exit)) ≤ 0
      exact Nat.le_of_eq (program_exact id (.finalizerOf captured exit))
    all_goals cases produced
  case scopeClose scope => cases produced; exact Nat.le_refl _
  case restoreCtx context => cases produced; exact Nat.le_refl _
  all_goals cases produced

/-- The actual installed native finalizer pays for its active note with its matching recorded start. -/
theorem native_start_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (machine : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (exit : ExitV) (body : NCode) (callback : EffName) (flag : Bool) (program : NCode)
    (owned : NameAt built.program callback)
    (selected : (WriterPhase.popFor fiber.frame exit).answer = .frame (.onExit body callback flag))
    (produced : (interpAt built.program machine.completedExits built.table).finalizerProgram callback
      ((WriterPhase.popFor fiber.frame exit).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (interpAt built.program machine.completedExits built.table)
      machine fiber yielding exit
    frame id next.fiber.frame + machine.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath id)) ≤
      frame id fiber.frame + next.machine.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath id)) ∧
      next.machine.state.refs = machine.state.refs := by
  have reserved := program_bound built admitted id member machine.completedExits callback
    ((WriterPhase.popFor fiber.frame exit).deliveredExit exit) program owned produced
  have same : Machine.WriterWeights.popFor fiber.frame exit = WriterPhase.popFor fiber.frame exit := by
    cases exit <;> rfl
  have installed := Machine.WriterWeights.native_start_bound (model id)
    (FinalizerRun.atPath (SourcePaths.requestPath id)) (interpAt built.program machine.completedExits built.table)
    machine fiber yielding exit body callback flag program (by rw [same]; exact selected) (by rw [same]; exact produced) (by
      rw [same]
      change current id (finalizerCode _ _ program) ≤ name id callback + _
      rw [restoring_count]
      exact reserved)
  refine ⟨?_, congrArg Stores.refs installed.2.2⟩
  have bounded := installed.1
  change frame id (evaluatePrim.finalizerOr (interpAt built.program machine.completedExits built.table) machine fiber yielding exit).fiber.frame ≤
    frame id fiber.frame + (if FinalizerRun.atPath (SourcePaths.requestPath id) callback then 1 else 0) at bounded
  have counted := installed.2.1
  change (evaluatePrim.finalizerOr (interpAt built.program machine.completedExits built.table) machine fiber yielding exit).machine.trace.countP
    (FinalizerRun.startedAt (SourcePaths.requestPath id)) = machine.trace.countP
    (FinalizerRun.startedAt (SourcePaths.requestPath id)) + (if FinalizerRun.atPath (SourcePaths.requestPath id) callback then 1 else 0) at counted
  rw [counted]
  omega

end Test.Dogfood.Scenario.Atomic.WriterFinalizers
