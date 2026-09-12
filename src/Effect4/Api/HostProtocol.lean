import Effect4.Api

/-! T-09: the finite host protocol, separate from Eff and the machine stores.
The transition table and record fields are data projected into the target and tape schema.
Receipt (`submit`) does not execute an answer; `answer` names explicit application.
Authority: Test/contracts/foundation-wave2.contract.md, T-09 / T-12 amendment.
-/
set_option autoImplicit false
namespace Effect4.Api.HostProtocol
open Effect4 Effect4.Machine Effect4.Program

inductive State
  | idle | awaitingAsync | parked | terminated
deriving DecidableEq, Repr

inductive Tag
  | submit | answer | advanceClock | cancel | schedule
deriving DecidableEq, Repr

/-- The scheduler's full decision remains in the tape; this labels its protocol edge. -/
inductive Label
  | submit (key : Key)
  | answer (key : Key)
  | advanceClock (millis : Nat)
  | cancel (fiber : FiberId)
  | schedule
deriving DecidableEq, Repr

def Label.tag : Label → Tag
  | .submit _ => .submit | .answer _ => .answer | .advanceClock _ => .advanceClock
  | .cancel _ => .cancel | .schedule => .schedule

structure Edge where
  source : State
  label : Tag
  target : State
deriving DecidableEq, Repr

inductive FieldType
  | natural | boolean | text | json
deriving DecidableEq, Repr

structure RecordShape where
  kind : String
  fields : List (String × FieldType)
deriving DecidableEq, Repr

structure Protocol where
  version : Nat
  initial : State
  states : List State
  transitions : List Edge
  records : List RecordShape
deriving DecidableEq, Repr

def states : List State := [.idle, .awaitingAsync, .parked, .terminated]

/-- Scheduler, clock, and cancellation steps can wake or finish fibers. Only an
outstanding external call admits receipt/application; receipt keeps the phase unchanged.
Terminal sessions admit only terminal controls. Guards and row types remain the existing
`requestOf` / `Envelope` checks, not a duplicate transition semantics. -/
def hostProtocol : Protocol where
  version := 2
  initial := .idle
  states := states
  transitions :=
    [⟨.awaitingAsync, .submit, .awaitingAsync⟩] ++
    states.map (⟨.awaitingAsync, .answer, ·⟩) ++
    [.idle, .awaitingAsync, .parked].flatMap (fun source =>
      [.advanceClock, .cancel, .schedule].flatMap (fun label =>
        states.map (⟨source, label, ·⟩))) ++
    [.advanceClock, .cancel, .schedule].map (⟨.terminated, ·, .terminated⟩)
  records :=
    [ ⟨"call", [("callId", .natural), ("fiber", .natural), ("token", .natural),
        ("row", .natural), ("request", .json)]⟩
    , ⟨"reply", [("callId", .natural), ("fiber", .natural), ("token", .natural),
        ("completion", .json)]⟩
    , ⟨"apply", [("fiber", .natural), ("token", .natural)]⟩
    , ⟨"advanceClock", [("millis", .natural)]⟩
    , ⟨"cancel", [("fiber", .natural)]⟩
    , ⟨"evaluate", [("fiber", .natural)]⟩
    , ⟨"fire", [("fiber", .natural)]⟩
    , ⟨"flush", []⟩
    , ⟨"yieldVerdict", [("fiber", .natural), ("verdict", .boolean)]⟩
    , ⟨"installMiddleware", []⟩ ]

def allows (source : State) (label : Label) (target : State) : Bool :=
  hostProtocol.transitions.contains ⟨source, label.tag, target⟩

/-- External awaits take priority over the aggregate terminal/parked observation.
This sees all fibers, including finalizers, rather than just the root's exit. -/
def observe (machine : Api.Machine) : State :=
  if !(awaits machine).isEmpty then .awaitingAsync
  else if machine.fibers.all (fun f => f.exit.isSome) then .terminated
  else if machine.fibers.any (fun f => f.exit.isNone && f.parked == .notParked) then .idle
  else .parked

def controlLabel : NativeDecision → Label
  | .advance millis => .advanceClock millis
  | .interruptFrom _ _ fiber => .cancel fiber
  | .answerAsync fiber token _ => .answer ⟨fiber, token⟩
  | _ => .schedule

end Effect4.Api.HostProtocol
