import Test.Dogfood.Scenario
import Effect4.Laws.Api.SessionMeaningLoop

/-! Finite controls for Q4/Q6b, proposed claim rows-loop-frontier, R6/R12.
See PLAN.md for placement. These are finite consumers of the landed waiting agreement. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Test.L4CleanupReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote
open Test.Dogfood.Scenario (Move Sel answer script ok failed live held refusals)

def errTy : Ty := .prod (.lit "ProbeError") .string
def fetch : RowDef := Row.host "Probe.fetch" .nat .nat errTy "cleanup review"
def close : RowDef := Row.host "Probe.close" .nat .unit errTy "cleanup review"

/-- Each iteration changes the reference before asking the host. -/
def program (reset : Bool := false) : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun cell =>
    onExitWith
      (forRange (nat 0) (nat 2) fun cursor =>
        andThen (Ref.set cell (app "succ" [cursor])) (Row.call fetch cursor))
      (fun _ =>
        let cleanup := bindWith (Ref.get cell) fun current => Row.call close current
        if reset then andThen (Ref.set cell (nat 0)) cleanup else cleanup)

def request (reset : Bool := false) : Module NativeOp :=
  { rows := [fetch, close], main := program reset }
def built (reset : Bool := false) : Option Effect4.Api.Built :=
  (Effect4.Api.Author.build (request reset)).toOption

def played (moves : List Move) (reset : Bool := false) : Option Run :=
  (built reset).map fun b => Test.Dogfood.Scenario.play (Run.open b "cleanup-review") moves

def beforeSecond : List Move := script [[.start], answer (.row "Probe.fetch") (ok (.nat 10))]
def duringCleanup : List Move := script [beforeSecond, answer (.row "Probe.fetch") (failed "ProbeError" "body")]
def finished : List Move := script [duringCleanup, answer (.row "Probe.close") (ok .unit)]
def failedCleanup : List Move := script [duringCleanup, answer (.row "Probe.close") (failed "ProbeError" "cleanup")]

def stopOf (s : Run) : Option RowsStop :=
  match s.exit with
  | some ex => some (.finished ex)
  | none => s.outstanding.head? >>= fun call =>
    match call.op with
    | .external row => some (.waiting row call.request)
    | _ => none

def observation (moves : List Move) (k : Nat) (reset : Bool := false) : Option (RowsObservation (List ExitV)) :=
  (played moves reset).map fun s =>
    observeRows (tapeHost s.built.table) (denoteRowsB s.built.table k s.built.program [])
      Stores.empty (Run.appliedExits s)

def ready (moves : List Move) (reset : Bool := false) : Bool :=
  match played moves reset with
  | none => false
  | some s => Run.funded s && Run.atRest s && Run.hostDriven s &&
    LoopedDataRows s.built.table s.built.program && !(StraightRows s.built.table s.built.program) &&
    (refusals s).isEmpty

def agrees (moves : List Move) (k : Nat) (reset : Bool := false) : Bool :=
  match played moves reset, observation moves k reset with
  | some s, some o => decide (some o.stop = stopOf s ∧ o.stores = s.machine.state ∧ o.host = [])
  | _, _ => false

def pending (moves : List Move) (reset : Bool := false) : Option (List (String × Val)) :=
  (played moves reset).map fun s => (live s).map fun call => (call.row, call.request)

def requests (moves : List Move) (reset : Bool := false) : Option (List (String × Val)) :=
  (played moves reset).map fun s => (held s).map fun call => (call.row, call.request)

#guard (built).isSome
#guard ready beforeSecond
#guard ready duringCleanup
#guard ready finished
#guard ready failedCleanup
#guard pending beforeSecond = some [("Probe.fetch", .nat 1)]
#guard requests beforeSecond = some [("Probe.fetch", .nat 0)]
#guard pending duringCleanup = some [("Probe.close", .nat 2)]
#guard (played duringCleanup).bind (·.exit) = none
#guard agrees beforeSecond 3
#guard agrees duringCleanup 3
#guard agrees duringCleanup 7
#guard agrees finished 3
#guard agrees failedCleanup 3
#guard (played finished).bind (·.exit) = some (.failure (.fail (.tagged "ProbeError" "body")))
#guard requests finished = some [("Probe.fetch", .nat 0), ("Probe.fetch", .nat 1), ("Probe.close", .nat 2)]

/-- A loop cut retains its earlier stores and remaining tape, without running cleanup. -/
def cutBeforeFailure : Bool :=
  match observation duringCleanup 1, observation duringCleanup 3 with
  | some cut, some wait => decide (cut.stop = .budget ∧ cut.host.length = 1 ∧ cut.stores ≠ wait.stores)
  | _, _ => false
#guard cutBeforeFailure
#guard !(agrees duringCleanup 1)

/- Destructive cleanup is admitted but changes its request and the retained stores.
An exit-only comparison cannot detect that mistake. -/
#guard ready duringCleanup true
#guard pending duringCleanup true = some [("Probe.close", .nat 0)]
#guard agrees duringCleanup 3 true
#guard (played finished true).bind (·.exit) = (played finished).bind (·.exit)
#guard (observation duringCleanup 3 true).map (·.stores) ≠ (observation duringCleanup 3).map (·.stores)

/-- The source address and checked reply type for the actual parked call. -/
def callView (moves : List Move) : Option (List Nat × CallInstance NativeOp) := do
  let s ← played moves
  let a ← s.outstanding.head?
  let origin ← Program.originOf s.machine a.fiber a.token
  let checked ← s.session.callInstance origin
  pure (origin, checked)

/-- Read the call's address from the same run that supplies its outstanding key. -/
def originMatches (moves : List Move) : Bool :=
  match played moves, callView moves with
  | some s, some (origin, checked) =>
    match (Node.eff s.built.program).at_ origin, s.outstanding.head? with
    | some (.eff (.perform op _)), some call => decide (op = call.op ∧ checked.op = op)
    | _, _ => false
  | _, _ => false

#guard originMatches beforeSecond
#guard originMatches duringCleanup
#guard (callView beforeSecond).map (fun c => c.2.answer) = some .nat
#guard (callView duringCleanup).map (fun c => c.2.answer) = some .unit
#guard (callView duringCleanup).map (fun c => c.2.error) = some errTy
#guard (callView beforeSecond).map Prod.fst ≠ (callView duringCleanup).map Prod.fst
#guard (callView finished).isNone

end Test.L4CleanupReview
