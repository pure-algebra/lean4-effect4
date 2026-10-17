import Test.Dogfood.Scenario.Atomic.Runs
import Test.Dogfood.Scenario.Atomic.Model
import Test.Dogfood.Scenario
import Effect4.Author
import Test.Dogfood.P4RateLimiter
import Test.Dogfood.P5LedgerService
import Effect4.Laws.Author

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
* **Controls.** `shopControls` and `aloneControls`: for each entry a green control and at least
  one red control. A control names the runs that its comparison reads. The red controls are the
  separate read and write of today, the store update erased while the answer stays, a finalizer
  that takes the deposit back, a finalizer that notes twice, and the answer and the state types
  swapped.
* **Lowered runs.** The program's rows carry binder terms that no name images. The program
  prints and reads back since the state plan's T5, part A (`Test/Dogfood/Scenario/Faces.lean`).
  The host lane and the engine's lane take their scripts from `runsOf`: the keyed lane performs
  each named run that a host can perform, and `Test/Dogfood/Scenario/TapeData.lean` names the runs
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

/-! ## 1. The claim -/

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

/-! ## 2. The runs and the controls -/

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
  match builtInputs with
  | some (b, _racy, _erased, _undone, _twice, suspended, plain, aloneUndone) => (runSet.runs, shopControls b ++ aloneControls b suspended plain aloneUndone)
  | none => ([], [green "bounded" "the shop and its variants build" [] fun _ => false])

/-! ## 3. The record -/

/-- The atomic scenario. The claim assembles the five clauses. The typing law of a
read-modify-write row is an associated law: the record claims no dependency of `atomic` on it. -/
def scenario : Scenario :=
  { name := runSet.name
    program := ``shop
    observation := ``observe
    runs := runsAndControls.1
    controls := runsAndControls.2 }

end Test.Dogfood.Scenario.Atomic

