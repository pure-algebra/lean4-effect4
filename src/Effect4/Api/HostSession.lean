import Effect4.Api.HostProtocol

/-!
A checked, keyed host-reply session over the existing Eff machine. The program and
row table are indexed by the existing admission certificate. Recorder call IDs are distinct
from machine guard tokens; `bindCall` is their checked association. No oracle answers are
loaded. This module owns no JSON decoder, host adequacy theorem or scheduling policy.
Authority: Test/contracts/foundation-wave2.contract.md, S6b host protocol.
-/

set_option autoImplicit false

namespace Effect4.Api.HostSession

open Effect4 Effect4.Machine Effect4.Program

abbrev Answer := Completion Val Err Defect FiberId Ann

abbrev Key := HostProtocol.Key

def version : Nat := HostProtocol.hostProtocol.version

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
  key : Key
  completion : Answer
deriving DecidableEq

def BoundCall.key (bound : BoundCall) : Key := ⟨bound.call.fiber, bound.token⟩

/-- Slots are created in binding order, so receipt changes a value without reordering
storage. The finite representation contains no function-valued map. -/
structure ReplySlot where
  key : Key
  reply : Option Reply
 deriving DecidableEq

def readReply : List ReplySlot → Key → Option Reply
  | [], _ => none
  | slot :: rest, key => if slot.key = key then slot.reply else readReply rest key

def storeReply (slots : List ReplySlot) (reply : Reply) : List ReplySlot :=
  slots.map fun slot => if slot.key = reply.key then { slot with reply := some reply } else slot

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
  active : List BoundCall := []
  pending : List ReplySlot := []
  consumed : List Nat := []
  retired : List RetiredCall := []

inductive Refusal
  | version
  | session
  | profile
  | table
  | program (reason : AdmitRefusal)
  | duplicateCall
  | protocol
  | selectionRequired
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
  else if s.active.any (fun bound => bound.key == ⟨call.fiber, token⟩) then refuse .duplicateCall
  else if call.callId ≠ s.nextCall then refuse .callOrder
  else if requestOf s.machine call.fiber token ≠ some (call.op, call.request) then
    refuse .staleCall
  else ⟨.bound, { s with
    active := s.active ++ [⟨call, token⟩]
    pending := s.pending ++ [⟨⟨call.fiber, token⟩, none⟩]
    nextCall := s.nextCall + 1 }⟩

/-- Pure preflight. Success establishes exactly the existing `Envelope` and returns only
its recorded answer decision. It neither applies a decision nor consumes a reply. -/
def preflight {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) : Except Refusal NativeDecision :=
  if reply.version ≠ version then .error .version
  else if reply.session ≠ s.header.session then .error .session
  else match s.active.find? (fun bound => bound.key == reply.key) with
    | none => .error .noCall
    | some bound =>
      if reply.callId ≠ bound.call.callId then .error .callOrder
      else if requestOf s.machine bound.call.fiber bound.token = none then .error .staleCall
      else match acceptReply table s.machine (bound.record reply) with
        | none => .error .envelope
        | some decision => .ok decision

/-- Pending completions in binding order; no application policy is inferred from this list. -/
def pendingReplies {program : Api.Program} {table : RowTable} (s : Session program table) : List Reply :=
  s.pending.filterMap ReplySlot.reply

/-- Receipt stores only. Another key may already have a pending completion. -/
def submit {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) : Result program table :=
  if (readReply s.pending reply.key).isSome then ⟨.refused .pendingReply, s⟩
  else match preflight s reply with
    | .error why => ⟨.refused why, s⟩
    | .ok _ =>
      if !(s.pending.any fun slot => slot.key == reply.key) then ⟨.refused .noCall, s⟩
      else if !HostProtocol.allows (HostProtocol.observe s.machine) (.submit reply.key)
          (HostProtocol.observe s.machine) then ⟨.refused .protocol, s⟩
      else ⟨.preflight, { s with pending := storeReply s.pending reply }⟩

/-- Retire every association whose exact guard was removed by a machine step. Shared
cancellation may retire more than the selected key. Accepted but unapplied payloads remain
available to the host cleanup driver, without consuming a machine allocation or a call. -/
def retire {program : Api.Program} {table : RowTable} (s : Session program table) : Session program table :=
  let dead := s.active.filter fun bound => (requestOf s.machine bound.call.fiber bound.token).isNone
  { s with
    active := s.active.filter fun bound => (requestOf s.machine bound.call.fiber bound.token).isSome
    pending := s.pending.filter fun slot => !(dead.any fun bound => bound.key == slot.key)
    retired := s.retired ++ dead.map (fun bound => ⟨bound, readReply s.pending bound.key⟩) }

/-- Execute one explicitly selected key. Zero fuel changes nothing. Consumption is counted
only after its exact guard disappears. The remaining continuations run in the tape's order;
this function is deliberately absent from the receipt commutation law. -/
def applyReply {program : Api.Program} {table : RowTable} (s : Session program table)
    (key : Key) : Nat → Result program table
  | 0 => ⟨.frontier, s⟩
  | fuel + 1 =>
    match s.active.find? (fun bound => bound.key == key), readReply s.pending key with
    | some bound, some reply =>
      match preflight s reply with
      | .error why => ⟨.refused why, s⟩
      | .ok decision =>
        let machine := steppedBy program (fuel + 1) table s.machine decision
        if !HostProtocol.allows (HostProtocol.observe s.machine) (.answer key)
            (HostProtocol.observe machine) then ⟨.refused .protocol, s⟩
        else if requestOf machine bound.call.fiber bound.token = none then
          let next := { s with
            machine := machine
            active := s.active.filter (fun b => b.key != key)
            pending := s.pending.filter (fun slot => slot.key != key)
            applied := s.applied + 1
            consumed := s.consumed ++ [bound.call.callId] }
          ⟨.applied, retire next⟩
        else ⟨.frontier, { s with machine }⟩
    | _, _ => ⟨.refused .noCall, s⟩

/-- Explicit compatibility convenience for a single pending completion. More than one
pending reply requires a key; arrival or binding order is never an implicit scheduler. -/
def applyPending {program : Api.Program} {table : RowTable} (s : Session program table) :
    Nat → Result program table
  | 0 => ⟨.frontier, s⟩
  | fuel + 1 => match pendingReplies s with
    | [reply] => applyReply s reply.key (fuel + 1)
    | [] => ⟨.refused .noCall, s⟩
    | _ => ⟨.refused .selectionRequired, s⟩

/-- Controls and reply applications are separate tape records. Pending replies do not
forbid scheduling other fibers. After any control, all removed associations are retired. -/
def advance {program : Api.Program} {table : RowTable} (s : Session program table)
    (fuel : Nat) (decision : NativeDecision) : Result program table :=
  match decision with
  | .answerAsync _ _ _ => ⟨.refused .directAnswer, s⟩
  | _ =>
    if s.machine.stuck.isSome then ⟨.refused .stuck, s⟩
    else
      letI := evaluatorFor program table
      let (machine, enough) := stepDecisionState (interpOf program table) fuel s.machine decision
      if !HostProtocol.allows (HostProtocol.observe s.machine) (HostProtocol.controlLabel decision)
          (HostProtocol.observe machine) then ⟨.refused .protocol, s⟩
      else ⟨if enough then .progressed else .frontier, retire { s with machine }⟩

/-- Reading a frontier does not execute pending replies or discard the session ledger. -/
def inspect {program : Api.Program} {table : RowTable} (s : Session program table) : Api.Run :=
  letI := evaluatorFor program table
  match replayEval (interpOf program table) 0 [] s.machine with
  | .finished m => ⟨.finished, m, []⟩
  | .frontier why m => ⟨.frontier, m, Api.frontierReasons why m⟩
  | .stuck why m => ⟨.stuck why, m, []⟩

end Effect4.Api.HostSession
