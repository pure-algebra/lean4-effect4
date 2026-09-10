import Effect4.Api

/-!
A checked, serialized host-reply session over the existing Eff machine. The program and
row table are indexed by the existing admission certificate. Recorder call IDs are distinct
from machine guard tokens; `bindCall` is their checked association. No oracle answers are
loaded. This module owns no JSON decoder, host adequacy theorem or scheduling policy.
Authority: Test/contracts/foundation-wave2.contract.md, S6b host protocol.
-/

set_option autoImplicit false

namespace Effect4.Api.HostSession

open Effect4 Effect4.Machine Effect4.Program

abbrev Answer := Completion Val Err Defect FiberId Ann

def version : Nat := 1

structure Header where
  version : Nat
  session : String
  profile : String
  table : RowTable
deriving DecidableEq, Repr

/-- Actual call-start claims. `fiber` is a recorded semantic fiber ID, not an implicit
conversion from a runtime fiber number. A binding must justify that association. -/
structure Call where
  version : Nat
  session : String
  table : RowTable
  callId : Nat
  fiber : FiberId
  op : NativeOp
  request : Val
deriving DecidableEq

/-- A recorder call paired with the separately checked replay guard. -/
structure BoundCall where
  call : Call
  token : Nat
deriving DecidableEq

structure Reply where
  version : Nat
  session : String
  callId : Nat
  completion : Answer
deriving DecidableEq

/-- The recorded claims come from the call record, not from the machine's expected call. -/
def BoundCall.record (bound : BoundCall) (reply : Reply) : RecordedReply :=
  ⟨bound.call.table, bound.call.fiber, bound.token, bound.call.op,
    bound.call.request, reply.completion⟩

/-- Retiring a cancelled association preserves any accepted but unapplied completion.
A resource binding must account for its cleanup; this record does not perform host cleanup. -/
structure RetiredCall where
  bound : BoundCall
  pending : Option Reply
deriving DecidableEq

structure Session (program : Api.Program) (table : RowTable) where
  admitted : AdmittedProgram program table
  header : Header
  machine : Api.Machine
  nextCall : Nat := 0
  applied : Nat := 0
  active : Option BoundCall := none
  pending : Option Reply := none
  consumed : List Nat := []
  retired : List RetiredCall := []

inductive Refusal
  | version
  | session
  | profile
  | table
  | program (reason : AdmitRefusal)
  | activeCall
  | pendingReply
  | callOrder
  | noCall
  | staleCall
  | envelope
  | directAnswer
  | pendingControl
  | stuck
  deriving DecidableEq, Repr

inductive Phase
  | bound
  | preflight
  | applied
  | progressed
  | frontier
  | refused (reason : Refusal)
  deriving DecidableEq, Repr

structure Result (program : Api.Program) (table : RowTable) where
  phase : Phase
  session : Session program table

/-- Validate an explicit header and retain the indexed admission proof. Empty session IDs
refuse. The expected profile is supplied by the binding's explicitly selected profile. -/
def start (program : Api.Program) (table : RowTable) (expectedProfile : String)
    (header : Header) (compileFuel : Nat) (choices : List Bool := []) :
    Except Refusal (Session program table) :=
  if header.version ≠ version then .error .version
  else if header.session = "" then .error .session
  else if header.profile ≠ expectedProfile then .error .profile
  else if header.table ≠ table then .error .table
  else match admitProgram program table with
    | .error why => .error (.program why)
    | .ok admitted => .ok { admitted, header, machine := Api.load program compileFuel choices [] }

def outstanding {program : Api.Program} {table : RowTable} (s : Session program table) :
    List Await := awaits s.machine

/-- Associate exactly the claims recorded at call start with an outstanding guard. The
next call ID is allocated here; completion application has a separate counter. -/
def bindCall {program : Api.Program} {table : RowTable} (s : Session program table)
    (call : Call) (token : Nat) : Result program table :=
  let refuse := fun why => ⟨.refused why, s⟩
  if call.version ≠ version then refuse .version
  else if call.session ≠ s.header.session then refuse .session
  else if call.table ≠ table then refuse .table
  else if s.active.isSome then refuse .activeCall
  else if s.pending.isSome then refuse .pendingReply
  else if call.callId ≠ s.nextCall then refuse .callOrder
  else if requestOf s.machine call.fiber token ≠ some (call.op, call.request) then
    refuse .staleCall
  else ⟨.bound, { s with active := some ⟨call, token⟩, nextCall := s.nextCall + 1 }⟩

/-- Pure preflight. Success establishes exactly the existing `Envelope` and returns only
its recorded answer decision. It neither applies a decision nor consumes a reply. -/
def preflight {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) : Except Refusal NativeDecision :=
  if reply.version ≠ version then .error .version
  else if reply.session ≠ s.header.session then .error .session
  else match s.active with
    | none => .error .noCall
    | some bound =>
      if reply.callId ≠ bound.call.callId then .error .callOrder
      else match acceptReply table s.machine (bound.record reply) with
        | none => .error .envelope
        | some decision => .ok decision

/-- Hold one preflighted completion until execution actually removes its exact guard. -/
def submit {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) : Result program table :=
  if s.pending.isSome then ⟨.refused .pendingReply, s⟩
  else match preflight s reply with
    | .error why => ⟨.refused why, s⟩
    | .ok _ => ⟨.preflight, { s with pending := some reply }⟩

/-- Zero fuel retains both the machine and the pending record. A positive application is
counted only if its exact guard disappeared, even when later command execution exhausted
fuel. If that guard survives, keep the resulting state and pending record as a frontier. -/
def applyPending {program : Api.Program} {table : RowTable} (s : Session program table) :
    Nat → Result program table
  | 0 => ⟨.frontier, s⟩
  | fuel + 1 =>
    match s.active, s.pending with
    | some bound, some reply =>
      match preflight s reply with
      | .error why => ⟨.refused why, s⟩
      | .ok decision =>
        let machine := steppedBy program (fuel + 1) table s.machine decision
        if requestOf machine bound.call.fiber bound.token = none then
          ⟨.applied, { s with machine, active := none, pending := none, applied := s.applied + 1, consumed := s.consumed ++ [bound.call.callId] }⟩
        else ⟨.frontier, { s with machine }⟩
    | _, _ => ⟨.refused .noCall, s⟩

/-- A control step cannot smuggle an unchecked answer. While a reply is pending only
explicit cancellation may move the machine. If cancellation removes an active guard, retain
its association and pending payload in `retired`; never mark it applied. -/
def advance {program : Api.Program} {table : RowTable} (s : Session program table)
    (fuel : Nat) (decision : NativeDecision) : Result program table :=
  match decision with
  | .answerAsync _ _ _ => ⟨.refused .directAnswer, s⟩
  | _ =>
    let cancellation := match decision with | .interruptFrom _ _ _ => true | _ => false
    if s.pending.isSome && !cancellation then ⟨.refused .pendingControl, s⟩
    else if s.machine.stuck.isSome then ⟨.refused .stuck, s⟩
    else
      letI := evaluatorFor program table
      let (machine, enough) := stepDecisionState (interpOf program table) fuel s.machine decision
      let next := { s with machine }
      let next := match s.active with
        | none => next
        | some bound =>
          if requestOf machine bound.call.fiber bound.token = none then
            { next with active := none, pending := none, retired := s.retired ++ [⟨bound, s.pending⟩] }
          else next
      ⟨if enough then .progressed else .frontier, next⟩

/-- Reading a frontier does not execute pending replies or discard the session ledger. -/
def inspect {program : Api.Program} {table : RowTable} (s : Session program table) : Api.Run :=
  letI := evaluatorFor program table
  match replayEval (interpOf program table) 0 [] s.machine with
  | .finished m => ⟨.finished, m⟩
  | .frontier m => ⟨.frontier, m⟩
  | .stuck why m => ⟨.stuck why, m⟩

end Effect4.Api.HostSession
