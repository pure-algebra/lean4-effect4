import Effect4.Laws.Program.AnswerSlots.TypedScopes
import Effect4.Laws.Program.AnswerSlots.InitializedSync
import Effect4.Laws.Program.NativeScopeFields

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initialized synchronous heads certify every newly stored release capture.
Reach: actual ref and gate allocation heads, source writer thunks and captured scope registrations.
Limit: the shared contextual command lift supplies the looked-up current frame and prior scope fields.
Consumer: crew command-scope preservation and the protected log-history producer.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- A protected source operation carries the fields its native scope registration stores. -/
theorem operation_fields (spec : Spec) (operation : SyncOp)
    (source : SourceScope.OpAt spec.root operation) (owned : OpAt spec operation) :
    Effect4.Machine.ScopeFields.OperationAt (scopeModel spec) operation := by
  cases operation
  case scopeAdd scope fin => exact owned
  case scopeMake strategy | scopeFork scope strategy => exact source
  all_goals trivial

/-- The actual native thunk projects its protected capture and source scope strategy. -/
theorem thunk_fields (spec : Spec) (thunk : EffThunk) (owned : ThunkAt spec thunk) :
    Effect4.Program.ScopeFields.ThunkAt (scopeModel spec) thunk := by
  cases thunk
  case op operation => exact operation_fields spec operation owned.1 owned.2.2
  case store stored =>
    cases stored
    case op operation => exact operation_fields spec operation owned.1 owned.2.2
    all_goals trivial
  all_goals trivial
end Effect4.Program.AnswerSlots.Typed

namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Initializer allocations and every stable synchronous head supply the actual scope-field permission. -/
theorem sync_fields (spec : Spec) (world : World) (kind : Kind) (thunk : EffThunk)
    (owned : CodeAt spec world kind (.sync thunk)) :
    Effect4.Program.ScopeFields.ThunkAt (Typed.scopeModel spec.toSpec) thunk := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage => exact (initial_not_sync spec world _ _ stage thunk same.symm).elim
  | allocating small stage | gateAllocating stage => cases same; trivial
  | stable ready held =>
    cases same
    exact Typed.thunk_fields spec.toSpec thunk held.2
  | frontier zero phase | yielding phase refs deferred pending | bound first callback | yieldThen phase held => cases same

/-- The shared contextual scope lift consumes permission from the actual current initialized code. -/
theorem current_fields (spec : Spec) (world : World) (kind : Kind) (program : NCode)
    (owned : CodeAt spec world kind program) :
    Effect4.Program.ScopeFields.CurrentAt (Typed.scopeModel spec.toSpec) program := by
  intro thunk same
  exact sync_fields spec world kind thunk (same ▸ owned)
end Effect4.Program.AnswerSlots.Initialized
