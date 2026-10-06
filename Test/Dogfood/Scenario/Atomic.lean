import Test.Dogfood.Scenario
import Test.Dogfood.P3WorkerQueue
import Test.Dogfood.P4RateLimiter
import Test.Dogfood.P5LedgerService
import Effect4.Laws.Program.MeaningEq
import Effect4.Laws.Program.Typed.Denotation

/-!
# The atomic scenario: one atomic update a request, a failure behind the commits, and a cleanup

Decisions row 254. The scenario extends the consumers of `Test/Dogfood/P4RateLimiter.lean` and
`Test/Dogfood/P5LedgerService.lean`: p4's `Window` cell with its atomic decision, and p5's
`Account` cell with its atomic deposit. Its straight consumer extends
`Test/Program/MeaningEqContract.lean`. It composes five features: two record cells with one
atomic read-modify-write row each, forked requests, a typed failure behind two commits, a
finalizer, and a refill on the logical clock.

* **Program.** `shop`: a rate-limited ledger. Each request decides in one store step over the
  window. An admitted request deposits its own number in one store step over the account, so a
  deposit's amount names its request. Request 2 fails behind both commits. Every request's
  finalizer notes the request and the count of decided requests it sees. A daemon refills the
  window every 1000 ms, and a sixth request comes after the first refill.
* **Script.** The root runs, the dispatchers drain, and the clock moves past the refill. Two
  hostile scripts interrupt a request, or the root, before a decision.
* **Observation.** `Observation`, five fields: each request's outcome, the whole window, the
  whole account, the count of completed requests, and the cleanup log.
* **Claim.** `atomic` assembles five clauses. Four are planned goals over every script:
  `bounded`, `counted`, `committed` and `cleans_once`. The fifth is proved, on the straight
  fragment: `unsuspended_runs`. One law stands beside them as an associated law: the typing of a
  read-modify-write row (`syncRow_typed`, a theorem of the law graph).
* **Controls.** `controls`: for each entry a green control and at least one red control. The red
  controls are the separate read and write of today, the store update erased while the answer
  stays, a finalizer that takes the deposit back, a finalizer that notes twice, and the answer
  and the state types swapped.
* **Lowered runs.** The program's rows carry binder terms that no name images, so the printer
  refuses it by name until the faces of a binder term land (the state plan's T5). The host run
  waits. The engine run is a fixture of `Test/Dogfood/Scenario/Tape.lean`.

One control of the brief is not here: a cleanup replayed under one registration. The cleanup
log counts writes by identity. It does not count a finalizer's invocations, so no run of this
battery shows one registration that ran twice. The red control of `cleans_once` is a finalizer
that writes twice in one invocation, and it controls the log's multiplicity only.

Each run is a finite probe: one script on the Lean machine.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Atomic

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote (Straight StraightEq)
open Test.Dogfood.P3WorkerQueue (ascribe)
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

/-- `Ref.update(log, xs => [...xs, x])`: one entry appended to a log cell. -/
def note (log x : TermSrc) : Src NativeOp :=
  Ref.update "xs" (app "append" [var "xs", app "cons" [x, app "nil" []]]) log

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

/-! ## 4. The claim -/

/-- The proposition of `bounded`. -/
def Bounded : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).used ≤ 3

/-- **Between refills the used capacity stays bounded.** Under every script the window's `used`
field is at most 3. Reach: the program `shop`, every script of the driver's alphabet, the
battery's budgets, natural-valued fields. A field that is not there reads as `0`, so the
statement does not say that the store is formed. It is an application invariant over p4's real
`Window` transition: one atomic update a request, and a refill that writes zero. It does not
establish a scheduler guarantee, a host transaction or a whole-run resource theorem. It does not
hold of a request that reads and writes in two steps: a red control. Concept `store-typing`, R4.
Consumer: the atomic scenario. Its controls are finite runs, and the seat's receipt records a
bounded search. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal bounded : Bounded

/-- The proposition of `counted`. -/
def Counted : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).counted = true

/-- **The stores count each request's outcome once.** Under every script the observation
satisfies `Observation.counted`. An admitted request's deposit stands once in the account, and a
rejected request has none. The window's counts hold every completed request. When all six are
completed, the counts are exactly the requests' outcomes. The deposit is per request: its amount
is the request's number. The window's part is by outcome: the record keeps two counts, and no
identity. Reach: the program `shop`, every script of the driver's alphabet, the battery's
budgets. A request that the script interrupts is not completed, and the statement leaves its
counts open. It does not establish that a request completes. Concept `store-typing`, R4.
Consumer: the atomic scenario. Its controls are finite runs, and the seat's receipt records a
bounded search. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal counted : Counted

/-- The proposition of `committed`. -/
def Committed : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    let o := observe (Scenario.play (opened b) moves)
    o.decisions[1]? = some .failedBehind → o.committed = true

/-- **A request that fails behind its commits leaves them in the stores.** Under every script,
once request 2 has exited with the planted failure, the observation satisfies
`Observation.committed`. Its deposit stands once in the account, the window counts an admitted
request, and its finalizer saw a decided request. Reach: the program `shop`, every script of the
driver's alphabet, the battery's budgets. The supporting law is
`Effect4.Program.Denote.meaning_onExit` (`src/Effect4/Laws/Program/Denote.lean`): a finalizer
runs on the stores its body left, and its own stores stay. That law holds of a finalizer that
takes the deposit back, and this statement does not: a red control. That law has no placement,
so the record does not list it. This statement does not establish a host transaction, that
request 2 fails, a whole-run resource theorem, or anything of a lowered run. Concept
`store-typing`, R4. Consumer: the atomic scenario. Its controls are finite runs, and the seat's
receipt records a bounded search. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal committed : Committed

/-- The proposition of `cleans_once`. -/
def CleansOnce : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).cleaned.Nodup

/-- **The cleanup log holds each request once.** Under every script no request's number stands
twice in the cleanup log. Reach: the program `shop`, every script of the driver's alphabet, the
battery's budgets. It is a statement about the log: it counts writes by identity. It does not
count a finalizer's invocations, and it shows no registration that ran twice. Its red control is
a finalizer that writes its entry twice in one invocation. It does not establish that a
finalizer runs. Concept `scope-lifetime-finalization`, R11. Consumer: the atomic scenario. Its
controls are finite runs, and the seat's receipt records a bounded search. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal cleans_once : CleansOnce

/-- A program without its suspensions, on the straight fragment's constructors. Any other node
stays as it is. -/
def unsuspend : NativeEff → NativeEff
  | .suspend b => unsuspend b
  | .bind a b => .bind (unsuspend a) (unsuspend b)
  | .select t d a b => .select t d (unsuspend a) (unsuspend b)
  | .exit b => .exit (unsuspend b)
  | .catchCause b h => .catchCause (unsuspend b) (unsuspend h)
  | .matchCause b v c => .matchCause (unsuspend b) (unsuspend v) (unsuspend c)
  | .onExit b f => .onExit (unsuspend b) (unsuspend f)
  | e => e

/-- A straight program and the program without its suspensions have one meaning. A step of the
registry claim `straight-composition-agreement`: it composes the congruences of `StraightEq`
(`src/Effect4/Laws/Program/MeaningEq.lean`). Its consumer is `unsuspended_runs`. -/
theorem unsuspend_eq (e : NativeEff) : Straight e = true → StraightEq e (unsuspend e) := by
  fun_induction unsuspend e with
  | case1 b ih => exact fun h => (StraightEq.suspend_remove b h).trans (ih h)
  | case2 a b iha ihb =>
    exact fun h => (iha (Bool.and_eq_true_iff.mp h).1).bind (ihb (Bool.and_eq_true_iff.mp h).2)
  | case3 t d a b iha ihb =>
    exact fun h =>
      StraightEq.select t d (iha (Bool.and_eq_true_iff.mp h).1) (ihb (Bool.and_eq_true_iff.mp h).2)
  | case4 b ih => exact fun h => (ih h).exit
  | case5 b c ihb ihc =>
    exact fun h =>
      (ihb (Bool.and_eq_true_iff.mp h).1).catchCause (ihc (Bool.and_eq_true_iff.mp h).2)
  | case6 b v c ihb ihv ihc =>
    exact fun h =>
      (ihb (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).matchCause
        (ihv (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2)
        (ihc (Bool.and_eq_true_iff.mp h).2)
  | case7 b f ihb ihf =>
    exact fun h => (ihb (Bool.and_eq_true_iff.mp h).1).onExit (ihf (Bool.and_eq_true_iff.mp h).2)
  | case8 e => exact fun h => StraightEq.refl e h

/-- The proposition of `unsuspended_runs`. -/
def Unsuspended : Prop :=
  ∀ (e : NativeEff), Straight e = true →
    (Api.run e (StraightEq.fuelFor e)).outcome = .finished ∧
      (Api.run (unsuspend e) (StraightEq.fuelFor (unsuspend e))).outcome = .finished ∧
      (Api.run e (StraightEq.fuelFor e)).exit =
        (Api.run (unsuspend e) (StraightEq.fuelFor (unsuspend e))).exit ∧
      (Api.run e (StraightEq.fuelFor e)).stores =
        (Api.run (unsuspend e) (StraightEq.fuelFor (unsuspend e))).stores

/-- **Removing a program's suspensions keeps its exit and its complete stores.** A straight
program and the program without its suspensions both finish, each at its own bound, with one
exit and the same stores. The stores are complete: they hold what a failure left and what a
finalizer wrote. Reach: the straight fragment (`Straight`), one fiber, the bound `fuelFor` of
each program. It consumes `StraightEq.run_agrees_at_bound`, so it is a consumer of the registry
claim `straight-composition-agreement`. It does not reach a program that forks, yields or
sleeps, as `shop` does. It does not compare traces, a budget below the bound, a host table or a
lowered run. Concept `translation-simulation`, R8. Consumer: the atomic scenario, on the failing
request alone (`alone`). -/
@[semantics "translation-simulation" (requirement := R8)]
theorem unsuspended_runs : Unsuspended :=
  fun e straight => (unsuspend_eq e straight).run_agrees_at_bound

/-- **The atomic scenario's claim.** Between refills the used capacity stays bounded. The stores
count each request's outcome once. A request that fails behind its commits leaves them in the
stores. The cleanup log holds each request once. Removing a straight program's suspensions keeps
its exit and its stores. The first four are planned goals, so this theorem is proved modulo
them. The fifth is proved. It does not establish a scheduler guarantee without a bound, a host
transaction or a whole-run resource theorem. -/
@[semantics "store-typing" (requirement := R4)]
theorem atomic : Bounded ∧ Counted ∧ Committed ∧ CleansOnce ∧ Unsuspended :=
  ⟨bounded, counted, committed, cleans_once, unsuspended_runs⟩

/-! ## 5. The controls -/

/-- A deposit entry of the account's history. -/
def deposit (amount : Nat) : Val := recordOf ["_tag", "amount"] [.str "Deposit", .nat amount]

/-- The account after the deposits of the given requests. -/
def accountOf (amounts : List Nat) : Option Val :=
  some (recordOf ["balance", "history", "id"]
    [.nat amounts.sum, .list (amounts.map deposit), .str "acc-1"])

/-- A `[request, count seen]` entry of the cleanup log. -/
def saw (id count : Nat) : Val := .list [.nat id, .nat count]

/-- After `started`: three admitted, two rejected, request 2 failed behind its commits. -/
def atStarted : Observation :=
  { decisions := [.admitted, .failedBehind, .admitted, .rejected, .rejected, .pending]
    window := some (windowVal 3 3 2)
    account := accountOf [1, 2, 3]
    completed := 5
    cleanups := [saw 1 1, saw 2 2, saw 3 3, saw 4 4, saw 5 5] }

/-- After `finished`: the refill freed the window, and the sixth request went through. -/
def atFinished : Observation :=
  { decisions := [.admitted, .failedBehind, .admitted, .rejected, .rejected, .admitted]
    window := some (windowVal 1 4 2)
    account := accountOf [1, 2, 3, 6]
    completed := 6
    cleanups := [saw 1 1, saw 2 2, saw 3 3, saw 4 4, saw 5 5, saw 6 6] }

/-- After `interrupted`: request 2 decided nothing, and request 4 took the third admission. -/
def atInterrupted : Observation :=
  { decisions := [.admitted, .interrupted none, .admitted, .admitted, .rejected, .pending]
    window := some (windowVal 3 3 1)
    account := accountOf [1, 3, 4]
    completed := 4
    cleanups := [saw 2 0, saw 1 1, saw 3 2, saw 4 3, saw 5 4] }

/-- Whether a script on a built program shows an observation. -/
def shows (b : Api.Built) (moves : List Move) (expected : Observation) : Bool :=
  observe (Scenario.play (opened b) moves) == expected

/-- A program's run at its own bound. -/
def atBound (e : NativeEff) : Api.Inspection := Api.run e (StraightEq.fuelFor e)

/-- The controls of the four clauses over the shop, from one build of each program. -/
def shopControls (b racy erased undone twice : Api.Built) : List Control :=
  let at' := fun (built : Api.Built) (moves : List Move) =>
    observe (Scenario.play (opened built) moves)
  [ -- between refills the used capacity stays bounded
    green "bounded" "before the refill three of five requests are admitted, and three are used"
      (shows b started atStarted)
  , green "bounded" "the refill writes zero, and the sixth request is admitted after it"
      (shows b refilled { atStarted with window := some (windowVal 0 3 2) } &&
        shows b finished atFinished)
  , red "bounded" "the separate read and write of today admits five and uses five"
      (shows racy started
        { atStarted with
          decisions := [.admitted, .failedBehind, .admitted, .admitted, .admitted, .pending]
          window := some (windowVal 5 5 0)
          account := accountOf [1, 2, 3, 4, 5] })
    -- the stores count each request's outcome once
  , green "counted" "six completed requests are four admitted with four deposits, and two rejected"
      ((at' b finished).counted && (at' b finished).completed == 6 &&
        (at' b finished).deposits == [1, 2, 3, 6])
  , green "counted"
      "an interrupted request is counted nowhere, and the next request takes its place"
      (shows b interrupted atInterrupted && (at' b interrupted).counted)
  , red "counted" "a term that answers the decision and leaves the window loses every count"
      (!(at' erased started).counted &&
        shows erased started
          { decisions := [.admitted, .failedBehind, .admitted, .admitted, .admitted, .pending]
            window := some (windowVal 0 0 0)
            account := accountOf [1, 2, 3, 4, 5]
            completed := 5
            cleanups := [saw 1 0, saw 2 0, saw 3 0, saw 4 0, saw 5 0] })
    -- a request that fails behind its commits leaves them in the stores
  , green "committed"
      "request 2 fails behind its commits: its deposit stands, and its finalizer saw two decided"
      ((at' b started).decisions[1]? == some .failedBehind && (at' b started).committed &&
        (at' b started).deposits == [1, 2, 3] && (at' b started).sawAt 2 == [2])
  , red "committed"
      "a finalizer that takes the deposit back leaves the failure and no deposit of request 2"
      ((at' undone started).decisions[1]? == some .failedBehind &&
        !(at' undone started).committed &&
        shows undone started { atStarted with account := accountOf [1, 3] })
    -- the cleanup log holds each request once
  , green "once" "each request that ran stands once in the cleanup log"
      ((at' b started).cleaned == [1, 2, 3, 4, 5] && (at' b finished).cleaned == requests)
  , green "once" "an interrupted request stands once, and a second interruption adds no entry"
      ((at' b interrupted).cleaned == [2, 1, 3, 4, 5] && (at' b interrupted).sawAt 2 == [0])
  , green "once" "with the root interrupted, each of the five requests stands once"
      ((at' b stopped).cleaned == [1, 2, 3, 4, 5] &&
        (at' b stopped).decisions.take 5 == List.replicate 5 (.interrupted (some ⟨0⟩)))
  , red "once" "a finalizer that notes twice leaves each request twice in the log"
      (!decide (at' twice started).cleaned.Nodup &&
        (at' twice started).cleaned == [1, 1, 2, 2, 3, 3, 4, 4, 5, 5])
    -- the typing of a read-modify-write row
  , green "typed row"
      "the request's row answers a boolean over a window cell: the shop builds at the window"
      ((b.ty.answer, b.ty.error) == (windowTy, .never))
  , red "typed row" "the answer and the next window swapped are refused at the term's result"
      ((typingReason? swapped).map (·.head) == some "resultNotSubtype") ]

/-- The controls of the straight clause, on the failing request alone. -/
def aloneControls (b suspended plain undone : Api.Built) : List Control :=
  let kept : List Val := [windowVal 1 1 0, (accountOf [2]).getD .unit, .list [saw 2 1]]
  [ green "rewrite"
      "the request alone without its suspensions is the one written without them, with the commits"
      (Straight suspended.program && unsuspend suspended.program == plain.program &&
        suspended.program != plain.program &&
        (atBound suspended.program).outcome == Api.Outcome.finished &&
        (atBound plain.program).outcome == Api.Outcome.finished &&
        (atBound suspended.program).exit == some downstream &&
        (atBound plain.program).exit == some downstream &&
        (atBound suspended.program).stores == (atBound plain.program).stores &&
        (atBound plain.program).stores.refs == kept)
  , red "rewrite" "a finalizer that takes the deposit back keeps the exit and changes the stores"
      (unsuspend undone.program != plain.program &&
        (atBound undone.program).exit == (atBound plain.program).exit &&
        (atBound undone.program).stores != (atBound plain.program).stores)
  , red "rewrite" "the shop forks and yields, so it is outside the straight fragment"
      (!Straight b.program) ]

/-- The scenario's controls. A program that does not build leaves one failing control. -/
def controls : List Control :=
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  match build (shop .none), build (shop .racy), build (shop .erased), build (shop .undone),
    build (shop .twice), build (alone .none true), build (alone .none false),
    build (alone .undone false) with
  | some b, some racy, some erased, some undone, some twice, some suspended, some plain,
      some aloneUndone =>
    shopControls b racy erased undone twice ++ aloneControls b suspended plain aloneUndone
  | _, _, _, _, _, _, _, _ => [green "bounded" "the shop and its variants build" false]

/-! ## 6. The record -/

/-- The atomic scenario. The claim assembles the five clauses. The typing law of a
read-modify-write row is an associated law: the record claims no dependency of `atomic` on it. -/
def scenario : Scenario :=
  { name := "atomic"
    program := ``shop
    observation := ``observe
    claim := ``atomic
    clauses :=
      [ ⟨"bounded", ``bounded⟩
      , ⟨"counted", ``counted⟩
      , ⟨"committed", ``committed⟩
      , ⟨"once", ``cleans_once⟩
      , ⟨"rewrite", ``unsuspended_runs⟩ ]
    laws := [⟨"typed row", ``Effect4.Program.Typed.syncRow_typed⟩]
    controls := controls }

#scenario_gate scenario

end Test.Dogfood.Scenario.Atomic
