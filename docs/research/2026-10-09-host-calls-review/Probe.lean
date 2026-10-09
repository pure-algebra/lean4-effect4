import Effect4.Api.Author
import Effect4.Laws.Api.SessionMeaning
import Effect4.Program.Profile

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace HostCallReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Api.HostSession (Answer Key Phase)

private def built? (p : Api.Program) (table : RowTable) : Option Api.Built :=
  (Api.Author.Internal.finishBuild p table []).toOption

def scalar : Row := Profile.Scalar.waitRow
def single : Api.Program := .perform (.external 0) (.lit (.nat 2))
def answer : Answer := .ofExit (.success (.nat 7))
def good : Run.Reactor Nat := fun _ _ n => some (answer, n + 1)
def bad : Run.Reactor Nat := fun _ _ n => some (.ofExit (.success (.str "bad")), n + 1)

-- The adapter proposed for H9, copied from the battery under review.
def reactorHandler {σ : Type} (table : RowTable) (r : Run.Reactor σ) :
    Effects.Handler (RowSig table) (StateT σ Option) where
  handle op := fun state =>
    match externalRow table op.1.val with
    | none => none
    | some row =>
      match r row op.2 state with
      | some (.ofExit ex, next) =>
        if externalAdmits table op.1.val (.ofExit ex) [] then some (ex, next) else none
      | _ => none

-- An independent total semantic handler for the single scalar operation.
def goodMeaning : Effects.Handler (RowSig [scalar]) (StateT Nat Option) where
  handle _ := fun n => some (.success (.nat 7), n + 1)

structure DriverReport where
  straight : Bool
  funded : Bool
  atRest : Bool
  hostDriven : Bool
  exit : Option ExitV
  hostState : Nat
  semanticExit : Option ExitV
  semanticState : Option Nat
  deriving DecidableEq

def driver (rounds : Nat) : Option DriverReport := do
  let b ← built? single [scalar]
  let actual := Run.runWith b good 0 "review" {} rounds
  let semantic := meaningUnder goodMeaning single [] Stores.empty 0
  pure {
    straight := StraightRows b.table b.program
    funded := Run.funded actual.1
    atRest := Run.atRest actual.1
    hostDriven := Run.hostDriven actual.1
    exit := actual.1.exit
    hostState := actual.2
    semanticExit := semantic.map (·.1.1)
    semanticState := semantic.map (·.2) }

#eval (driver 0).map fun r => (r.straight, r.funded, r.atRest, r.hostDriven, r.exit.isSome, r.hostState, r.semanticExit.isSome, r.semanticState)
#eval (driver 4).map fun r => (r.straight, r.funded, r.atRest, r.hostDriven, r.exit.isSome, r.hostState, r.semanticExit.isSome, r.semanticState)
#guard driver 0 = some ⟨true, true, true, true, none, 0, some (.success (.nat 7)), some 1⟩
#guard driver 4 = some ⟨true, true, true, true, some (.success (.nat 7)), 1,
  some (.success (.nat 7)), some 1⟩

-- The generic row and source are the independent API fixture's admitted shape.
def first : Row :=
  { name := "first", spelling := "L.first", kind := .async, registration := .external,
    request := .list (.var 0), answer := .option (.var 0), cite := "review" }
def generic : Api.Program :=
  .bind (.succeed (.app "cons" (.cons (.lit (.nat 1)) (.cons (.app "nil" .nil) .nil))))
    (.perform (.external 0) (.var 0))
def firstHost : Run.Reactor Nat := fun _ _ n => some (.ofExit (.success (.some (.nat 1))), n + 1)

def genericReport : Option DriverReport := do
  let b ← built? generic [first]
  let actual := Run.runWith b firstHost 0 "generic"
  let semantic := meaningUnder (reactorHandler b.table firstHost) b.program [] Stores.empty 0
  pure {
    straight := StraightRows b.table b.program
    funded := Run.funded actual.1
    atRest := Run.atRest actual.1
    hostDriven := Run.hostDriven actual.1
    exit := actual.1.exit
    hostState := actual.2
    semanticExit := semantic.map (·.1.1)
    semanticState := semantic.map (·.2) }

#eval genericReport.map fun r => (r.straight, r.funded, r.atRest, r.hostDriven, r.exit.isSome, r.hostState, r.semanticExit.isSome, r.semanticState)
#guard genericReport = some ⟨true, true, true, true, some (.success (.some (.nat 1))), 1, none, none⟩

-- This is lost frontier information, not a refutation of equality after both sides become none.
def refusedState : Option (Option ExitV × Nat × Bool × Bool) := do
  let b ← built? single [scalar]
  let actual := Run.runWith b bad 0 "bad"
  pure (actual.1.exit, actual.2,
    (meaningUnder (reactorHandler b.table bad) b.program [] Stores.empty 0).isNone,
    actual.1.phases.contains (.refused .envelope))
#eval refusedState.map fun (ex, n, semanticNone, refused) => (ex.isNone, n, semanticNone, refused)
#guard refusedState = some (none, 1, true, true)

structure LifecycleReport where
  waitingBeforeBind : Nat
  activeBeforeBind : Nat
  nextBeforeBind : Nat
  activeAfter : Nat
  pendingAfter : Nat
  consumedAfter : List Nat
  originAfterAbsent : Bool
  retiredPayloadKept : Bool
  secondApply : Phase
  replaySnapshotApply : Phase
  deriving Repr, DecidableEq

def lifecycle : Option LifecycleReport := do
  let b ← built? single [scalar]
  let start := (Run.open b "lifecycle").play Rows.start
  let key : Key := ⟨Api.root, 0⟩
  let received := start.receive key answer
  let applied := received.step (.apply key)
  let cancelled := received.control (.interruptFrom none .empty Api.root)
  pure {
    waitingBeforeBind := start.outstanding.length,
    activeBeforeBind := start.session.active.length,
    nextBeforeBind := start.session.nextCall,
    activeAfter := applied.session.active.length,
    pendingAfter := applied.session.pending.length,
    consumedAfter := applied.session.consumed,
    originAfterAbsent := (Program.originOf applied.machine Api.root 0).isNone,
    retiredPayloadKept := cancelled.session.retired.any (·.pending.isSome),
    secondApply := (Api.HostSession.applyReply applied.session key 1000).phase,
    replaySnapshotApply := (Api.HostSession.applyReply received.session key 1000).phase }
#eval lifecycle
#guard lifecycle = some ⟨1, 0, 0, 0, 0, [0], true, true, .refused .noCall, .applied⟩

-- This comparison uses existing execution routes, not the proposed optimized binding.
def immediateReport : Bool × Bool × Nat × Nat :=
  let immediate := Api.run single 100 [answer] [scalar]
  let parked := Api.replay single 100 [Api.evaluate, .answerAsync Api.root 0 answer] [] [scalar]
  (decide (immediate.exit = parked.exit), decide (immediate.machine.trace = parked.machine.trace),
    immediate.machine.trace.length, parked.machine.trace.length)
#eval immediateReport
#guard immediateReport.1 = true
#guard immediateReport.2.1 = false

-- This adapter leaves membership at the session's checked application boundary.
def rawExitHandler {σ : Type} (table : RowTable) (r : Run.Reactor σ) :
    Effects.Handler (RowSig table) (StateT σ Option) where
  handle op := fun state =>
    match externalRow table op.1.val with
    | none => none
    | some row =>
      match r row op.2 state with
      | some (.ofExit ex, next) => some (ex, next)
      | _ => none

def genericRaw : Option (ExitV × Nat) := do
  let b ← built? generic [first]
  (meaningUnder (rawExitHandler b.table firstHost) b.program [] Stores.empty 0).map
    fun result => (result.1.1, result.2)
#guard genericRaw = some (.success (.some (.nat 1)), 1)

-- Calls have machine order, binding order, and explicit application order.
def opts : Supervision.ForkOptions := { daemon := false, startImmediately := true, maskMode := .inherit }
def twoCalls : Api.Program :=
  .bind (.withFiber (.fork (.perform (.external 0) (.lit (.nat 2))) opts))
    (.bind (.withFiber (.fork (.perform (.external 0) (.lit (.nat 3))) opts))
      (.bind (.awaitFiber (.var 0) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))
def bindingOrder : Option (List Nat × List Nat × List Nat) := do
  let b ← built? twoCalls [scalar]
  let start := (Run.open b "order").play Rows.start
  let reversed := (start.receive ⟨⟨2⟩, 1⟩ answer).receive ⟨⟨1⟩, 0⟩ answer
  pure (start.outstanding.map (·.token), reversed.session.pending.map (·.key.token),
    reversed.session.active.map (·.call.callId))
#eval bindingOrder
#guard bindingOrder = some ([0, 1], [1, 0], [0, 1])

end HostCallReview
