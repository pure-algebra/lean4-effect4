import Test.Dogfood.Proofs.HostTimeoutCommands
import Effect4.Laws.Program.TyDecls

/-!
# Timeout reference values through native evaluation

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the reached command assertion and exact external reply admission.
The reached `ConfigurationAt` assertion retains a number or list at each cell's outer level.
The general host envelope admits delayed reads, so this source heap assertion is necessary.
The assertion does not restrict host replies or claim progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutHeap
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands

/-- A timeout cell's outer shape fails the actual host row's string membership check. -/
theorem outer_not_string {decls : TyDecls} {value : Val} (outer : OuterValue value)
    (allocated : List String) : Val.memberIn decls value .string allocated = false := by
  cases decls with
  | nil => cases outer <;> rfl
  | cons d ds =>
    apply Bool.eq_false_iff.mpr
    intro member
    obtain ⟨m, hm, step⟩ := hasTyIn_eq_true_iff.mp member
    rw [show Ty.members .string = [.string] from rfl, List.mem_singleton] at hm
    subst hm
    rcases step with ⟨_, _, unfolds, _⟩ | ⟨_, ps, obligations, _⟩
    · cases unfolds
    · cases outer <;> cases obligations

/-- The actual string answer row refuses every delayed read from Timeout's cells. -/
theorem read_refused (decls : TyDecls) (row : Row) (machine : Effect4.Program.NativeMachine)
    (fiber : FiberId) (token : Nat) (cell : RefKey) (answer : row.answer = .string)
    (heap : OuterHeap machine.state.refs) :
    admitAnswer decls row machine fiber token (.ofRefGet cell) ≠ none := by
  unfold admitAnswer
  dsimp only
  cases found : machine.state.refs[cell.index]? with
  | none => exact Option.some_ne_none _
  | some value =>
    have outer := heap value (List.mem_of_getElem? found)
    dsimp only
    rw [answer, outer_not_string outer]
    exact Option.some_ne_none _

/-- Timeout's general row envelope cannot admit a delayed reference read. -/
theorem delayed_read_refused {app : SigApp} (rows : app.rows = Test.Dogfood.Scenario.Timeout.fetch.table)
    (machine : Effect4.Program.NativeMachine) (fiber : FiberId)
    (token : Nat) (cell : RefKey) (heap : OuterHeap machine.state.refs) :
    admit app machine (.answerAsync fiber token (.ofRefGet cell)) ≠ none := by
  intro admitted
  have refused := read_refused app.types
  unfold admit at admitted
  rw [rows] at admitted
  repeat' split at admitted
  all_goals aesop (add safe forward [row_answer, refused])

/-- An admitted Timeout completion is an exit, with its exact success value or arbitrary cause. -/
theorem envelope_exit {app : SigApp} (rows : app.rows = Test.Dogfood.Scenario.Timeout.fetch.table)
    (machine : Effect4.Program.NativeMachine) (reply : RecordedReply)
    (heap : OuterHeap machine.state.refs) (accepted : Envelope app machine reply) :
    ∃ exit, reply.completion = .ofExit exit := by
  cases received : reply.completion with
  | ofExit exit => exact ⟨exit, rfl⟩
  | ofRefGet cell =>
    have admitted := accepted.2.2
    rw [received] at admitted
    exact (delayed_read_refused rows machine reply.fiber reply.token cell heap admitted).elim

/-- The instance fallback also keeps completions as exits without restricting their causes. -/
theorem instance_envelope_exit (app : SigApp) (instanceAt : List Nat → Option (CallInstance NativeOp))
    (machine : Effect4.Program.NativeMachine) (reply : RecordedReply)
    (accepted : InstanceEnvelope app instanceAt machine reply) :
    ∃ exit, reply.completion = .ofExit exit := by
  cases received : reply.completion with
  | ofExit exit => exact ⟨exit, rfl⟩
  | ofRefGet cell =>
    obtain ⟨index, row, origin, call, _, _, _, _, _, _, admitted⟩ := accepted.2.2
    rw [received] at admitted
    cases admitted

end Test.Dogfood.Proofs.HostTimeoutHeap

/- Finite admission control: the general string row accepts a delayed read of a stored string. -/
#guard Effect4.Program.admitAnswer [] Test.Dogfood.P1HttpCache.getQuote.row
    { Effect4.Api.load Test.Dogfood.Proofs.HostTimeoutSource.program 0 with
      state := { Effect4.Machine.Stores.empty with refs := [Effect4.Store.Val.str "later"] } }
    ⟨0⟩ 0 (.ofRefGet ⟨0⟩) = none

/- Finite admission readers: Timeout's number/list outer shapes fail the same string column. -/
#guard Effect4.Program.admitAnswer [] Test.Dogfood.P1HttpCache.getQuote.row
    { Effect4.Api.load Test.Dogfood.Proofs.HostTimeoutSource.program 0 with
      state := { Effect4.Machine.Stores.empty with refs := [Effect4.Store.Val.nat 0] } }
    ⟨0⟩ 0 (.ofRefGet ⟨0⟩) = some (.answerType ⟨0⟩ 0 .string)
#guard Effect4.Program.admitAnswer [] Test.Dogfood.P1HttpCache.getQuote.row
    { Effect4.Api.load Test.Dogfood.Proofs.HostTimeoutSource.program 0 with
      state := { Effect4.Machine.Stores.empty with refs := [Effect4.Store.Val.list []] } }
    ⟨0⟩ 0 (.ofRefGet ⟨0⟩) = some (.answerType ⟨0⟩ 0 .string)
