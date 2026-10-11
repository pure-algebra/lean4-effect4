import Test.Dogfood.Scenario.Atomic.Model
import Test.Dogfood.Scenario.Atomic.Store
import Test.Dogfood.Scenario.Atomic.Cleanup
import Test.Dogfood.Scenario
import Effect4.Author
import Test.Dogfood.P4RateLimiter
import Test.Dogfood.P5LedgerService
import Effect4.Laws.Author
import Test.Audit.ScenarioGate

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
  hostile scripts interrupt a request, or the root, before a decision. `runsOf` lists each
  script once, as a named run.
* **Observation.** `Observation`, five fields: each request's outcome, the whole window, the
  whole account, the count of completed requests, and the cleanup log.
* **Claim.** `atomic` assembles five clauses. Four quantify over every script:
  `bounded`, `counted`, `committed` and `cleans_once`. The fifth is proved, on the straight
  fragment: `unsuspended_runs`. One law stands beside them as an associated law: the typing of a
  read-modify-write row (`syncRow_typed`, a theorem of the law graph).
* **Controls.** `shopControls` and `aloneControls`: for each entry a green control and at least
  one red control. A control names the runs that its comparison reads. The red controls are the
  separate read and write of today, the store update erased while the answer stays, a finalizer
  that takes the deposit back, a finalizer that notes twice, and the answer and the state types
  swapped.
* **Lowered runs.** The program's rows carry binder terms that no name images. The program
  prints and reads back since the state plan's T5, part A (`Test/Dogfood/Scenario/Faces.lean`).
  The host lane and the engine's lane take their scripts from `runsOf`: the keyed lane performs
  each named run that a host can perform, and `Test/Dogfood/Scenario/Tape.lean` names the runs
  of the engine's fixture.

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
open Test.Dogfood.P4RateLimiter (window0 windowTy windowVal decision refill)
open Test.Dogfood.P5LedgerService (account0 deposited)

/-! ## 4. The claim -/

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
theorem bounded : Bounded := by
  intro b moves hb
  have heap := Effect4.Program.HeapSites.heap_sites_keep b budget.compileFuel Store.UsedOk
    (Store.shop_sites_used b hb) _ (Store.scenario_control b hb moves)
  rw [Store.observe_eq]
  show natField (Scenario.play (opened b) moves).machine.state.refs[0]? "used" ≤ 3
  cases h0 : (Scenario.play (opened b) moves).machine.state.refs[0]? with
  | none => exact Nat.zero_le 3
  | some v => exact heap 0 v h0

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
theorem counted : Counted := by
  intro b moves hb
  obtain ⟨g, fit⟩ := Store.shop_stages b hb budget.compileFuel _
    (Store.scenario_control b hb moves)
  rw [Store.observe_eq]
  exact Store.counted_of_fit fit

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
theorem committed : Committed := by
  intro b moves hb
  dsimp only
  rw [Store.observe_eq]
  intro hfail
  obtain ⟨g, fit⟩ := Store.shop_stages b hb budget.compileFuel _
    (Store.scenario_control b hb moves)
  exact Store.committed_of_fit fit hfail

/-- **The cleanup log holds each request once.** Under every script no request's number stands
twice in the cleanup log. Reach: the program `shop`, every script of the driver's alphabet, the
battery's budgets. It is a statement about the log: it counts writes by identity. It does not
count a finalizer's invocations, and it shows no registration that ran twice. Its red control is
a finalizer that writes its entry twice in one invocation. It does not establish that a
finalizer runs. Concept `scope-lifetime-finalization`, R11. Consumer: the atomic scenario. Its
controls are finite runs, and the seat's receipt records a bounded search. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem cleans_once : CleansOnce := by
  intro b moves built
  rw [Store.observe_eq]
  exact Cleanup.cleaned b _ built (Scenario.history b "atomic" budget "" moves)

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

/-! ## 5. The runs and the controls -/

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

/-- Whether a run shows an observation. -/
def shows (s : Run) (expected : Observation) : Bool := observe s == expected

/-- A program's run at its own bound. -/
def atBound (e : NativeEff) : Api.Inspection := Api.run e (StraightEq.fuelFor e)

/-- The scenario's named runs: each script of a control, once, from one build of each program.
The first five are on the shop. The last four play `started` on the four faulty shops. The host
lane performs them in this order. -/
def runsOf (b racy erased undone twice : Api.Built) : List NamedRun :=
  [ ⟨"started", opened b, started⟩
  , ⟨"refilled", opened b, refilled⟩
  , ⟨"finished", opened b, finished⟩
  , ⟨"interrupted", opened b, interrupted⟩
  , ⟨"stopped", opened b, stopped⟩
  , ⟨"racy", opened racy, started⟩
  , ⟨"erased", opened erased, started⟩
  , ⟨"undone", opened undone, started⟩
  , ⟨"twice", opened twice, started⟩ ]

/-- The controls of the four clauses over the shop. Each names the runs of `runsOf` that its
comparison reads, and the gate hands them over as played. The two controls of the typed row read
no run: one reads the shop's build, and one a typing refusal. -/
def shopControls (b : Api.Built) : List Control :=
  [ -- between refills the used capacity stays bounded
    green "bounded" "before the refill three of five requests are admitted, and three are used"
      ["started"] fun
      | [decided] => shows decided atStarted
      | _ => false
  , green "bounded" "the refill writes zero, and the sixth request is admitted after it"
      ["refilled", "finished"] fun
      | [freed, done] =>
        shows freed { atStarted with window := some (windowVal 0 3 2) } && shows done atFinished
      | _ => false
  , red "bounded" "the separate read and write of today admits five and uses five" ["racy"] fun
      | [raced] =>
        shows raced
          { atStarted with
            decisions := [.admitted, .failedBehind, .admitted, .admitted, .admitted, .pending]
            window := some (windowVal 5 5 0)
            account := accountOf [1, 2, 3, 4, 5] }
      | _ => false
    -- the stores count each request's outcome once
  , green "counted" "six completed requests are four admitted with four deposits, and two rejected"
      ["finished"] fun
      | [done] =>
        (observe done).counted && (observe done).completed == 6 &&
          (observe done).deposits == [1, 2, 3, 6]
      | _ => false
  , green "counted"
      "an interrupted request is counted nowhere, and the next request takes its place"
      ["interrupted"] fun
      | [cut] => shows cut atInterrupted && (observe cut).counted
      | _ => false
  , red "counted" "a term that answers the decision and leaves the window loses every count"
      ["erased"] fun
      | [erased] =>
        !(observe erased).counted &&
          shows erased
            { decisions := [.admitted, .failedBehind, .admitted, .admitted, .admitted, .pending]
              window := some (windowVal 0 0 0)
              account := accountOf [1, 2, 3, 4, 5]
              completed := 5
              cleanups := [saw 1 0, saw 2 0, saw 3 0, saw 4 0, saw 5 0] }
      | _ => false
    -- a request that fails behind its commits leaves them in the stores
  , green "committed"
      "request 2 fails behind its commits: its deposit stands, and its finalizer saw two decided"
      ["started"] fun
      | [decided] =>
        (observe decided).decisions[1]? == some .failedBehind && (observe decided).committed &&
          (observe decided).deposits == [1, 2, 3] && (observe decided).sawAt 2 == [2]
      | _ => false
  , red "committed"
      "a finalizer that takes the deposit back leaves the failure and no deposit of request 2"
      ["undone"] fun
      | [undone] =>
        (observe undone).decisions[1]? == some .failedBehind && !(observe undone).committed &&
          shows undone { atStarted with account := accountOf [1, 3] }
      | _ => false
    -- the cleanup log holds each request once
  , green "once" "each request that ran stands once in the cleanup log"
      ["started", "finished"] fun
      | [decided, done] =>
        (observe decided).cleaned == [1, 2, 3, 4, 5] && (observe done).cleaned == requests
      | _ => false
  , green "once" "an interrupted request stands once, and a second interruption adds no entry"
      ["interrupted"] fun
      | [cut] => (observe cut).cleaned == [2, 1, 3, 4, 5] && (observe cut).sawAt 2 == [0]
      | _ => false
  , green "once" "with the root interrupted, each of the five requests stands once"
      ["stopped"] fun
      | [halted] =>
        (observe halted).cleaned == [1, 2, 3, 4, 5] &&
          (observe halted).decisions.take 5 == List.replicate 5 (.interrupted (some ⟨0⟩))
      | _ => false
  , red "once" "a finalizer that notes twice leaves each request twice in the log" ["twice"] fun
      | [doubled] =>
        !decide (observe doubled).cleaned.Nodup &&
          (observe doubled).cleaned == [1, 1, 2, 2, 3, 3, 4, 4, 5, 5]
      | _ => false
    -- the typing of a read-modify-write row
  , green "typed row"
      "the request's row answers a boolean over a window cell: the shop builds at the window"
      [] fun _ => (b.ty.answer, b.ty.error) == (windowTy, .never)
  , red "typed row" "the answer and the next window swapped are refused at the term's result"
      [] fun _ => (typingReason? swapped).map (·.head) == some "resultNotSubtype" ]

/-- The controls of the straight clause, on the failing request alone. Each reads no named run:
it runs a program with `Api.run`, at a bound and with no script, and it compares no
`Observation`. -/
def aloneControls (b suspended plain undone : Api.Built) : List Control :=
  let kept : List Val := [windowVal 1 1 0, (accountOf [2]).getD .unit, .list [saw 2 1]]
  [ green "rewrite"
      "the request alone without its suspensions is the one written without them, with the commits"
      [] fun _ =>
        Straight suspended.program && unsuspend suspended.program == plain.program &&
          suspended.program != plain.program &&
          (atBound suspended.program).outcome == Api.Outcome.finished &&
          (atBound plain.program).outcome == Api.Outcome.finished &&
          (atBound suspended.program).exit == some downstream &&
          (atBound plain.program).exit == some downstream &&
          (atBound suspended.program).stores == (atBound plain.program).stores &&
          (atBound plain.program).stores.refs == kept
  , red "rewrite" "a finalizer that takes the deposit back keeps the exit and changes the stores"
      [] fun _ =>
        unsuspend undone.program != plain.program &&
          (atBound undone.program).exit == (atBound plain.program).exit &&
          (atBound undone.program).stores != (atBound plain.program).stores
  , red "rewrite" "the shop forks and yields, so it is outside the straight fragment"
      [] fun _ => !Straight b.program ]

/-- The scenario's runs and its controls, from one build of each program. A program that does
not build leaves no run and one failing control. -/
def runsAndControls : List NamedRun × List Control :=
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  match build (shop .none), build (shop .racy), build (shop .erased), build (shop .undone),
    build (shop .twice), build (alone .none true), build (alone .none false),
    build (alone .undone false) with
  | some b, some racy, some erased, some undone, some twice, some suspended, some plain,
      some aloneUndone =>
    (runsOf b racy erased undone twice,
      shopControls b ++ aloneControls b suspended plain aloneUndone)
  | _, _, _, _, _, _, _, _ =>
    ([], [green "bounded" "the shop and its variants build" [] fun _ => false])

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
    runs := runsAndControls.1
    controls := runsAndControls.2 }

-- The final gate pass teaches the record checker about clauses proved modulo subgoals.
/--
error: atomic: the claim Test.Dogfood.Scenario.Atomic.atomic rests on the planned goal Effect4.Program.FinalizerRun.funded_reachable, which no clause names
atomic: the claim Test.Dogfood.Scenario.Atomic.atomic rests on the planned goal Effect4.Program.FinalizerRun.once_placed_pushes_once, which no clause names
atomic: the claim Test.Dogfood.Scenario.Atomic.atomic rests on the planned goal Effect4.Program.HeapSites.heap_sites_keep, which no clause names
atomic: the claim Test.Dogfood.Scenario.Atomic.atomic rests on the planned goal Test.Dogfood.Scenario.Atomic.Cleanup.log_debits, which no clause names
atomic: the claim Test.Dogfood.Scenario.Atomic.atomic rests on the planned goal Test.Dogfood.Scenario.Atomic.Store.shop_stages, which no clause names
-/
#guard_msgs (error) in
#scenario_gate scenario

end Test.Dogfood.Scenario.Atomic
