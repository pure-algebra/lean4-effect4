import Effect4.Laws.Program.RowProtocol
import H9Controls
import TypedReplies

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace RowProtocolReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Run
open HostGeneralizationH9Review
open Test.Run.RunContract (twice)

def scalarOp (request : Val) : (RowSig twice.table).Op := ⟨⟨0, by decide⟩, request⟩

-- The new guard keeps the returned state of accepted answers and refuses a wrong shape.
#guard (show Option (ExitV × Nat) from (guardRows twice.table host).answer (scalarOp (.nat 2)) 0) =
  some (.success (.nat 2), 1)
#guard (show Option (ExitV × Nat) from (guardRows twice.table host).answer (scalarOp (.nat 3)) 1) =
  some (.success (.nat 4), 2)
#guard (guardRows twice.table badHost).answer (scalarOp (.nat 2)) 0 = none
#guard rowAdmits twice.table (scalarOp (.nat 2)) (.success (.str "wrong")) = false

-- Readers of the generic guard laws at the concrete host.
example : (guardRows twice.table host).Meets (rowProtocol twice.table) :=
  guardRows_meets twice.table host
example : guardRows twice.table (guardRows twice.table host) = guardRows twice.table host :=
  guardRows_of_meets twice.table (guardRows_meets twice.table host)

-- Actual admission along the recorded two-call machine tape.
private theorem admitted :
    RowsAdmit completed.built.table completed.built.program completed.budget.fuel
      (tapeOf completed) (Api.load completed.built.program completed.budget.compileFuel) := by
  constructor
  · intro i v h
    have e : some (NativeOp.external 0, Val.nat 2) = some (NativeOp.external i, v) := h
    cases e
    rfl
  constructor
  · intro i v h
    have e : some (NativeOp.external 0, Val.nat 3) = some (NativeOp.external i, v) := h
    cases e
    rfl
  trivial

private theorem answered :
    HostAnswered completed.built.table host completed.built.program completed.budget.fuel
      (tapeOf completed) (Api.load completed.built.program completed.budget.compileFuel) 0 2 :=
  hostAnsweredCheck_sound completed.built.table host completed.built.program completed.budget.fuel
    (tapeOf completed) (Api.load completed.built.program completed.budget.compileFuel) 0 2
    (by decide +kernel)

-- Consumer of the new transfer law: apply H9 under the guarded host.
example : hostRun (guardRows completed.built.table host) completed.built.program [] Stores.empty 0 =
    some (.success (.nat 4), (completed.machine.state, 2)) :=
  denoteRows_eq_session_host completed
    (Reached.play opened commands (Reached.open twice "session-A" budget))
    (by decide) (by decide) (by decide) (by decide)
    (guardRows completed.built.table host) 0 2
    (hostAnswered_guardRows completed.built.table host completed.built.program completed.budget.fuel
      (tapeOf completed) (Api.load completed.built.program completed.budget.compileFuel) 0 2
      answered admitted)
    (.success (.nat 4)) (by decide)

-- Scope control: an existing session admits its checked numeric instance.
-- The template guard deliberately refuses this same reply.
def instanceHost : Effects.Comodel (RowSig Test.Api.TypedReplies.table) Nat :=
  ⟨fun _ st => some (.success (.some (.nat 1)), st + 1)⟩
def instanceOp : (RowSig Test.Api.TypedReplies.table).Op :=
  ⟨⟨0, by decide⟩, .list [.nat 1]⟩
#guard Test.Api.TypedReplies.bound.map
  (fun s => (Api.HostSession.submit s Test.Api.TypedReplies.some1).phase) = some .preflight
#guard (guardRows Test.Api.TypedReplies.table instanceHost).answer instanceOp 0 = none

-- Scope control: allocation admission is not membership of the raw reply.
def handleRow : Row :=
  { name := "allocate", spelling := "Review.allocate", kind := .async, registration := .external,
    request := .unit, answer := .handle "Review.Resource", cite := "review" }
def handleOp : (RowSig [handleRow]).Op := ⟨⟨0, by decide⟩, .unit⟩
def allocatingHost : Effects.Comodel (RowSig [handleRow]) Nat :=
  ⟨fun _ st => some (.success (.nat st), st + 1)⟩
#guard rowAdmits [handleRow] handleOp (.success (.nat 0))
#guard !Val.hasTy (.nat 0) handleRow.answer []
#guard externalValue handleRow.answer [] (.nat 0) =
  some (["Review.Resource"], Value.external 0)
#guard (show Option (ExitV × Nat) from (guardRows [handleRow] allocatingHost).answer handleOp 0) = some (.success (.nat 0), 1)
-- With one allocation, session admission expects the next index; the fixed empty table cannot see it.
#guard externalAdmits [handleRow] 0 (.ofExit (.success (.nat 1))) ["Review.Resource"]
#guard !rowAdmits [handleRow] handleOp (.success (.nat 1))
#guard (guardRows [handleRow] allocatingHost).answer handleOp 1 = none

-- A missing request can make RowsAdmit vacuous. HostAnswered still requires the actual request.
def noRequestMachine : Api.Machine := Api.load (.succeed (.lit .unit)) 100
example : RowsAdmit twice.table (.succeed (.lit .unit)) 100
    [.answerAsync Api.root 99 (.ofExit (.success (.str "wrong")))] noRequestMachine := by
  constructor
  · intro i v h
    have e : (none : Option (NativeOp × Val)) = some (.external i, v) := h
    cases e
  trivial
example : ¬ HostAnswered twice.table badHost (.succeed (.lit .unit)) 100
    [.answerAsync Api.root 99 (.ofExit (.success (.str "wrong")))] noRequestMachine 0 1 := by
  intro h
  obtain ⟨i, v, _, _, hrequest, _, _⟩ := h
  have e : (none : Option (NativeOp × Val)) = some (.external i, v) := hrequest
  cases e

#eval (((show Option (ExitV × Nat) from (guardRows twice.table host).answer (scalarOp (.nat 3)) 1).map (fun result => result.2)),
  rowAdmits [handleRow] handleOp (.success (.nat 0)),
  Val.hasTy (.nat 0) handleRow.answer [])
end RowProtocolReview
