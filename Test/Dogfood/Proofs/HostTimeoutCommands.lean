import Test.Dogfood.Proofs.HostTimeoutEvaluation
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Agreement.Calls

/-!
# Timeout values at native command boundaries

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the complete command assertion lifted over `Run.Frame.HistoryOf`.
The stored frames keep ordered value classes at every command boundary.
A queued resume owes a matching class only when its fiber still holds its exact guard.
Reserved keys and command owners protect these conditions through later command steps.
The command assertion must also cover race exits, dispatcher tasks and timer resumes.
These local cases establish neither complete history closure nor progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutCommands
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation Effect4.Laws.Auto

/-- Every stored native frame has an ordered path to a body answer. -/
def FrameLedger (B : List Val) (machine : Effect4.Program.NativeMachine) : Prop :=
  ∀ fiber ∈ machine.fibers, FrameKind B .body fiber.frame

/-- An exact guard match supplies code at the input class of that fiber's actual saved stack. -/
def ResumeAt (B : List Val) (machine : Effect4.Program.NativeMachine) (id : FiberId) (token : Nat)
    (answer : NCode) : Prop :=
  ∀ fiber, machine.fiber? id = some fiber → fiber.parked = .withGuard token →
    ∃ input, CodeAt B input answer ∧ StackAt B input .body fiber.frame.stack

/-- Read a stored assertion at the actual native fiber lookup. -/
theorem FrameLedger.lookup {B : List Val} {machine : Effect4.Program.NativeMachine}
    (held : FrameLedger B machine) {id : FiberId} {fiber : NativeFiber}
    (found : machine.fiber? id = some fiber) : FrameKind B .body fiber.frame :=
  held fiber (List.mem_of_find?_eq_some found)

/-- Installing one classified frame retains all other stored frame assertions. -/
theorem FrameLedger.update {B : List Val} {machine : Effect4.Program.NativeMachine}
    (held : FrameLedger B machine) (fiber : NativeFiber) (owned : FrameKind B .body fiber.frame) :
    FrameLedger B (machine.update fiber) :=
  Guard.update_all machine fiber (fun f => FrameKind B .body f.frame) held owned

/-- Emitting machine events does not alter a stored value assertion. -/
theorem FrameLedger.emit {B : List Val} {machine : Effect4.Program.NativeMachine}
    (held : FrameLedger B machine) (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    FrameLedger B (machine.emit events) := held

/-- A fresh compiled timeout starts before any body-bearing environment slot exists. -/
theorem load (B : List Val) (fuel : Nat) : FrameLedger B (Api.load HostTimeoutSource.program fuel) := by
  intro fiber member
  have equal := List.mem_singleton.mp member
  subst fiber
  refine ⟨.body, ?_, .nil .body⟩
  have root := CodeAt.source (rootPoint fuel) (EnvAt.start (B := B))
  exact root

/-- A held external call's saved stack expects a reply body. -/
theorem external_stack {B : List Val} {frame : NativeFrame} (owned : FrameKind B .body frame)
    (op : NativeOp) (request : Val)
    (external : Guard.externalRequest frame.current = some (op, request)) :
    StackAt B .body .body frame.stack := by
  obtain ⟨input, code, stack⟩ := owned
  have head := code_head code
  generalize current : frame.current = next at head external
  cases head
  all_goals aesop (add norm simp [Guard.externalRequest])

/-- Timeout's host table contains only the declared string answer row. -/
theorem fetch_table : Test.Dogfood.Scenario.Timeout.fetch.table = [Test.Dogfood.P1HttpCache.getQuote.row] := by
  kernel_rfl

/-- Every resolved host answer column of the actual fetch is a string. -/
theorem row_answer (index : Nat) (row : Row)
    (found : externalRow Test.Dogfood.Scenario.Timeout.fetch.table index = some row) : row.answer = .string := by
  cases index with
  | zero =>
    have table : externalRow Test.Dogfood.Scenario.Timeout.fetch.table 0 =
        some Test.Dogfood.P1HttpCache.getQuote.row.normalizeTypes := by kernel_rfl
    rw [table] at found
    cases found
    rfl
  | succ index =>
    have absent : externalRow Test.Dogfood.Scenario.Timeout.fetch.table (index + 1) = none := by
      rw [fetch_table]
      simp only [externalRow, List.getElem?_cons_succ, List.getElem?_nil]
      rfl
    rw [absent] at found
    cases found

/-- Preparing an exit reply at Timeout's actual table keeps the exact value and stores. -/
theorem prepare_exit (current : Option NCode) (exit : ExitV) (state : Stores) :
    prepareExternalAnswer Test.Dogfood.Scenario.Timeout.fetch.table current (.ofExit exit) state =
      (state, Prim.ofExit exit) := by
  have present : Test.Dogfood.Scenario.Timeout.fetch.table.isEmpty = false := by kernel_rfl
  unfold prepareExternalAnswer
  simp only [present, Bool.false_eq_true, ite_false]
  cases exit with
  | failure cause =>
    split
    · rename_i impossible
      cases Completion.ofExit.inj impossible
    · rfl
  | success value =>
    split
    · rename_i index request path flag cancel received matching
      have equal := Exit.success.inj (Completion.ofExit.inj matching)
      subst received
      cases row : externalRow Test.Dogfood.Scenario.Timeout.fetch.table index with
      | none => rfl
      | some entry =>
        dsimp only
        cases result : externalValue entry.answer state.externals.allocated value with
        | none => rfl
        | some prepared =>
          have same := Agreement.externalValue_data
            (fun target unequal => by
              have answer := row_answer index entry row
              rw [unequal] at answer
              cases answer) result
          rw [same]
          rfl
    · rfl

/-- A queued exit reply has the exact class owed by its still-held external guard. -/
theorem exit_resume {B : List Val} (machine : Effect4.Program.NativeMachine) (id : FiberId)
    (token : Nat) (op : NativeOp) (request : Val) (exit : ExitV)
    (held : FrameLedger B machine) (call : requestOf machine id token = some (op, request))
    (body : ExitAt B .body exit) : ResumeAt B machine id token (Prim.ofExit exit) := by
  intro fiber found parked
  obtain ⟨owner, lookup, _, external⟩ := Guard.requestOf_shape call
  have equal := Option.some.inj (lookup.symm.trans found)
  subst owner
  exact ⟨.body, exit_code body, external_stack (held.lookup found) op request external⟩

/-- The actual token-matched resume uses precisely the queued code and saved continuation chain. -/
theorem resume_command {B : List Val} (machine : Effect4.Program.NativeMachine) (id : FiberId) (token : Nat)
    (answer : NCode) (rest : List Guard.NCmd) (held : FrameLedger B machine)
    (response : ResumeAt B machine id token answer) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    FrameLedger B (driveStep (interpOf HostTimeoutSource.program
      Test.Dogfood.Scenario.Timeout.fetch.table) machine (.resume id token answer) rest).1 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  unfold driveStep
  dsimp only
  split
  · exact held
  · rename_i fiber found
    cases parked : fiber.parked with
    | notParked => exact held
    | withGuard guard =>
      dsimp only
      split
      · rename_i same
        have response := response fiber found (by rw [parked, same])
        obtain ⟨input, code, stack⟩ := response
        apply FrameLedger.emit
        apply FrameLedger.update held
        exact ⟨input, code, stack⟩
      · exact held

end Test.Dogfood.Proofs.HostTimeoutCommands
