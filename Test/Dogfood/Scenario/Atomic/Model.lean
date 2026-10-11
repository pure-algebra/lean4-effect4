import Test.Dogfood.Scenario
import Effect4.Author
import Test.Dogfood.P4RateLimiter
import Test.Dogfood.P5LedgerService
import Effect4.Laws.Author

/-!
# The atomic scenario's program and observation

These are the source, scripts and propositions consumed by the Atomic proof and controls.
The extraction changes no definition. The claim remains in `Scenario/Atomic.lean`.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Atomic

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote (Straight StraightEq)
open Test.Dogfood.P4RateLimiter (window0 windowTy windowVal decision refill)
open Test.Dogfood.P5LedgerService (account0 deposited)

/-! ## 1. The program -/

/-- The fault a red control plants in a request. -/
inductive Fault
  /-- The scenario's program. -/
  | none
  /-- The separate read and write of today: the request reads the window, yields, then writes. -/
  | racy
  /-- The store update erased: the term answers the decision and leaves the window. -/
  | erased
  /-- The failing request's finalizer takes its deposit back. -/
  | undone
  /-- The finalizer notes its entry twice. -/
  | twice
deriving DecidableEq

/-- The request's decision over the window. The scenario's is p4's: one `Ref.modify` that
decides and rewrites the window in one store step. With `yielding`, a yield comes before the
step, never inside it. -/
def admit (fault : Fault) (yielding : Bool) (window : TermSrc) : Src NativeOp :=
  let step : Src NativeOp :=
    match fault with
    | .racy => eff do
        let w ← Ref.get window
        let _ ← yieldNow 0
        ifElse (app "lt" [field w "used", nat 3])
          (andThen (Ref.update "x"
              (recordSet (recordSet (var "x") "used" (app "succ" [field (var "x") "used"]))
                "admitted" (app "succ" [field (var "x") "admitted"])) window)
            (succeed (bool true)))
          (andThen (Ref.update "x"
              (recordSet (var "x") "rejected" (app "succ" [field (var "x") "rejected"])) window)
            (succeed (bool false)))
    | .erased =>
      Ref.modify "w" (app "pair" [app "lt" [field (var "w") "used", nat 3], var "w"]) window
    | _ => Ref.modify "w" (decision (var "w")) window
  if yielding then andThen (yieldNow 0) step else step

/-- A request's body. It decides over the window. When admitted, it deposits its number: p5's
atomic deposit, which answers the new balance. With `failing`, it then fails, so its failure
stands behind both commits. It answers its decision. -/
def body (fault : Fault) (yielding : Bool) (id : Nat) (failing : Bool) (window account : TermSrc) :
    Src NativeOp := eff do
  let admitted ← admit fault yielding window
  ifElse admitted
    (eff do
      let _ ← Ref.modify "a"
        (app "pair" [app "add" [field (var "a") "balance", nat id], deposited (var "a") (nat id)])
        account
      (if failing then fail (app "pair" [str "Downstream", str "unavailable"])
        else succeed (bool true)))
    (succeed (bool false))

/-- A request's finalizer. It notes the request's number and the count of decided requests it
sees. The fault `twice` notes that entry a second time. The fault `undone` makes the failing
request's finalizer take the last deposit back. -/
def finalizer (fault : Fault) (id : Nat) (failing : Bool) (window account cleaned : TermSrc) :
    Src NativeOp := eff do
  let w ← Ref.get window
  let seen := app "pair" [nat id, app "add" [field w "admitted", field w "rejected"]]
  let _ ← note cleaned seen
  let _ ← (if fault == .twice then note cleaned seen else succeed unit)
  (if fault == .undone && failing then
    Ref.update "a"
      (recordSet (recordSet (var "a") "balance" (app "sub" [field (var "a") "balance", nat id]))
        "history" (app "take" [field (var "a") "history",
          app "pred" [app "length" [field (var "a") "history"]]])) account
   else succeed unit)

/-- One request with a number: its body under its finalizer. -/
def request (fault : Fault) (id : Nat) (failing : Bool) (window account cleaned : TermSrc) :
    Src NativeOp :=
  onExit "exit" (body fault true id failing window account)
    (finalizer fault id failing window account cleaned)

/-- The shop: the window, the account and the cleanup log, in allocation order. A daemon refills
the window. Five requests run at once, and request 2 fails behind its commits. The root waits
for their exits, sleeps past the first refill, runs a sixth request and stops the daemon. -/
def shop (fault : Fault) : Module NativeOp := program (eff do
  let window ← Ref.make window0
  let account ← Ref.make account0
  let cleaned ← Ref.make (ascribe (.list (.prod .nat .nat)) (app "nil" []))
  let refiller ← daemon (refill window)
  let f1 ← fork (request fault 1 false window account cleaned)
  let f2 ← fork (request fault 2 true window account cleaned)
  let f3 ← fork (request fault 3 false window account cleaned)
  let f4 ← fork (request fault 4 false window account cleaned)
  let f5 ← fork (request fault 5 false window account cleaned)
  let _ ← await f1
  let _ ← await f2
  let _ ← await f3
  let _ ← await f4
  let _ ← await f5
  let _ ← Effect.sleep (nat 1500)
  let f6 ← fork (request fault 6 false window account cleaned)
  let _ ← await f6
  let _ ← withFiber (Action.interrupt refiller)
  Ref.get window)

/-- The failing request alone, on one fiber: no fork, no yield and no clock. With `suspended`,
its body and its finalizer are suspended computations. It is the straight consumer's program. -/
def alone (fault : Fault) (suspended : Bool) : Module NativeOp := program (eff do
  let window ← Ref.make window0
  let account ← Ref.make account0
  let cleaned ← Ref.make (ascribe (.list (.prod .nat .nat)) (app "nil" []))
  let wrap := fun (e : Src NativeOp) => if suspended then suspend e else e
  onExit "exit" (wrap (body fault false 2 true window account))
    (wrap (finalizer fault 2 true window account cleaned)))

/-- The answer and the next window swapped in the request's term. -/
def swapped : Module NativeOp :=
  program (bindName "s" (Ref.make window0) fun s =>
    Ref.modify "w" (app "pair" [var "w", app "lt" [field (var "w") "used", nat 3]]) s)

/-! ## 2. The scripts -/

/-- The budgets of every run of this battery. -/
def budget : Api.Budget := { fuel := 2000, compileFuel := 2000 }

/-- A built program opened under the scenario's name. -/
def opened (b : Api.Built) : Run := Run.open b "atomic" budget

/-- The root runs and every dispatcher drains: the five requests decide before any refill. -/
def started : List Move := [.start, .flush]

/-- The clock reaches the first refill. -/
def refilled : List Move := script [started, [.tick 1000]]

/-- The clock reaches the root's wake: the sixth request runs, and the root exits. -/
def finished : List Move := script [refilled, [.tick 500]]

/-- A hostile script: the host interrupts request 2, on fiber 3, before any request decides.
A second interruption follows its exit. -/
def interrupted : List Move := [.start, .cancel ⟨3⟩, .flush, .cancel ⟨3⟩]

/-- A hostile script: the host interrupts the root before any request decides. -/
def stopped : List Move := [.start, .cancel ⟨0⟩, .flush]

/-! ## 3. The observation -/

/-- The planted failure of request 2. -/
def downstream : ExitV := .failure (Cause.fail (.tagged "Downstream" "unavailable"))

/-- A request's outcome, read from its fiber's exit. An interruption's annotations are not part
of it. -/
inductive RequestOutcome
  /-- No exit yet. -/
  | pending
  /-- The answer `true`: the window admitted the request, and it deposited. -/
  | admitted
  /-- The answer `false`: the window rejected the request. -/
  | rejected
  /-- The planted failure, which a request reaches only behind its deposit. -/
  | failedBehind
  /-- An interruption, by a fiber or by the host. -/
  | interrupted (interruptor : Option FiberId)
  /-- Any other exit. -/
  | other
deriving DecidableEq

/-- The outcome an exit shows. -/
def outcomeOf (exit : Option ExitV) : RequestOutcome :=
  if exit == some downstream then .failedBehind
  else match exit with
    | none => .pending
    | some (.success (.bool true)) => .admitted
    | some (.success (.bool false)) => .rejected
    | some (.success _) => .other
    | some (.failure cause) =>
      match cause.reasons with
      | [Reason.interrupt interruptor _] => .interrupted interruptor
      | _ => .other

/-- Whether an outcome is an admitted one: the answer `true`, or the planted failure. -/
def RequestOutcome.isAdmitted (outcome : RequestOutcome) : Bool :=
  outcome == .admitted || outcome == .failedBehind

/-- The scenario's one observation. -/
structure Observation where
  /-- Each request's outcome, requests 1 to 6. -/
  decisions : List RequestOutcome
  /-- The whole `Window` record. -/
  window : Option Val
  /-- The whole `Account` record. -/
  account : Option Val
  /-- The count of completed requests: an admitted outcome or the rejected one. An interrupted
  request is not completed. -/
  completed : Nat
  /-- The cleanup log: each `[request, count seen]` the finalizers noted, in order. -/
  cleanups : List Val
deriving DecidableEq

/-- The requests' numbers, in the order of `Observation.decisions`. -/
def requests : List Nat := [1, 2, 3, 4, 5, 6]

/-- The fibers of requests 1 to 6: the daemon is fiber 1. -/
def requestFibers : List FiberId := [⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩]

/-- The entries of a log cell. -/
def entries : Option Val → List Val
  | some (.list values) => values
  | _ => []

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  let decisions := requestFibers.map fun fiber =>
    outcomeOf ((s.machine.fiber? fiber).bind RunFiber.exit)
  { decisions := decisions
    window := cell s 0
    account := cell s 1
    completed := (decisions.filter fun outcome => outcome.isAdmitted || outcome == .rejected).length
    cleanups := entries (cell s 2) }

/-- A natural field of a record, `0` when the record or the field is not there. -/
def natField (record : Option Val) (name : String) : Nat :=
  match record.bind fun value => Record.read false value name with
  | some (.nat n) => n
  | _ => 0

/-- The window's three counts. -/
def Observation.used (o : Observation) : Nat := natField o.window "used"
def Observation.admitted (o : Observation) : Nat := natField o.window "admitted"
def Observation.rejected (o : Observation) : Nat := natField o.window "rejected"

/-- The deposits: the amounts of the account's history, in order. A request deposits its own
number, so an amount names its request. -/
def Observation.deposits (o : Observation) : List Nat :=
  (entries (o.account.bind fun value => Record.read false value "history")).filterMap fun entry =>
    match Record.read false entry "amount" with
    | some (.nat amount) => some amount
    | _ => none

/-- The cleanup identities: the request's number of each entry of the cleanup log, in order. -/
def Observation.cleaned (o : Observation) : List Nat :=
  o.cleanups.filterMap fun entry =>
    match entry with
    | .list [.nat id, _] => some id
    | _ => none

/-- The counts of decided requests that the cleanup entries of one request saw. -/
def Observation.sawAt (o : Observation) (id : Nat) : List Nat :=
  o.cleanups.filterMap fun entry =>
    match entry with
    | .list [.nat i, .nat seen] => if i == id then some seen else none
    | _ => none

/-- Whether the stores count each request's outcome once. Three parts.

* Each request's own outcome is in the account: an admitted request's deposit stands once, a
  rejected request has none, and no request has two.
* The window's two outcome counts hold every completed request, the six requests bound them, and
  every deposit is an admitted request's.
* When all six requests are completed, the counts are exactly the requests' outcomes, and every
  admitted request has deposited. -/
def Observation.counted (o : Observation) : Bool :=
  let admittedOnes := (o.decisions.filter RequestOutcome.isAdmitted).length
  let rejectedOnes := (o.decisions.filter (· == .rejected)).length
  ((o.decisions.zip requests).all fun (outcome, id) =>
    if outcome.isAdmitted then o.deposits.count id == 1
    else if outcome == .rejected then o.deposits.count id == 0
    else decide (o.deposits.count id ≤ 1)) &&
  decide (admittedOnes ≤ o.admitted) && decide (rejectedOnes ≤ o.rejected) &&
  decide (o.admitted + o.rejected ≤ 6) && decide (o.deposits.length ≤ o.admitted) &&
  o.deposits.all requests.contains &&
  (o.completed != 6 ||
    (o.admitted == admittedOnes && o.rejected == rejectedOnes &&
      o.deposits.length == o.admitted))

/-- Whether the stores show request 2's commits: its deposit stands once in the account, the
window counts an admitted request, and its cleanup entry saw a decided request. -/
def Observation.committed (o : Observation) : Bool :=
  o.deposits.count 2 == 1 && decide (1 ≤ o.admitted) &&
    (o.sawAt 2).any fun seen => decide (1 ≤ seen)

/-- The proposition of `bounded`. -/
def Bounded : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).used ≤ 3

/-- The proposition of `counted`. -/
def Counted : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).counted = true

/-- The proposition of `committed`. -/
def Committed : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    let o := observe (Scenario.play (opened b) moves)
    o.decisions[1]? = some .failedBehind → o.committed = true

/-- The proposition of `cleans_once`. -/
def CleansOnce : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).cleaned.Nodup

end Test.Dogfood.Scenario.Atomic
