import Test.Dogfood.Scenario.Timeout.Model
import Test.Dogfood.Proofs.HostTimeoutHistory

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Timeout

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario
open Test.Dogfood.P1HttpCache (getQuote timeoutForm retryForm retryable)

/-! ## 4. The claim -/

/-- The original reply-based claim, retained as a refuted proposition.
An applied success can yield before the attempt exits, allowing the timer to win. -/
def ReplyBasedRetriesDeclared : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    moves.all Move.plain = true →
    (observe (Scenario.play (opened b) moves)).replyBasedRetriesDeclared = true

/-- The proposition of `retries_declared`. -/
def RetriesDeclared : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    moves.all Move.plain = true →
    (observe (Scenario.play (opened b) moves)).retriesDeclared = true

/-- **Only returned declared failures retry.** Each later attempt follows a completed timeout
form that returns a declared typed failure. The client starts at most four attempts.
Reach: `fetch`, the battery's budgets, and every plain script.
The observation keeps host reply application separate from the form's complete returned exit.
The selected entrant identifies its attempt or timer role at the actual exit observer.
The statement establishes no fairness, physical deadline, or general law of either form.
Concept: translation-simulation, R10. Consumer: the timeout scenario. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal retries_declared : RetriesDeclared

/-- The proposition of `stale_never_applies`. -/
def StaleNeverApplies : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    (observe (Scenario.play (opened b) moves)).staleNeverApplies = true

/-- **A reply of a timed-out attempt never applies to a later attempt.** Under every script the
observation satisfies `Observation.staleNeverApplies`. A retired call has no reply application,
no key has two receipts or two applications, and the root answers only the body of a reply that
was applied at its own call. Reach: the program `fetch`, every script of the driver's alphabet
with its raw rows, the battery's budgets. The key's identity carries it: a later attempt parks
under another fiber and another guard token. It does not establish reply admission at the
application, or the retirement edge of the host protocol: both are open parts of R6. It says
nothing of a host that answers the second call with the first call's body by its own choice.
Concept `host-session-protocol`, R6. Consumer: the timeout scenario. Its controls are finite
runs, and the seat's receipt records a bounded search. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem stale_never_applies : StaleNeverApplies := by
  intro built moves checked
  have clauses := Test.Dogfood.Proofs.HostJournal.stale_clauses built moves
  unfold Observation.staleNeverApplies
  rw [clauses.1, clauses.2.1, clauses.2.2]
  simp only [Bool.true_and]
  cases returned : (observe (Scenario.play (opened built) moves)).root with
  | running => rfl
  | answered body => exact Test.Dogfood.Proofs.HostTimeoutHistory.successful_body_seen built moves checked body returned
  | failed tag message => rfl
  | interrupted => rfl
  | other => rfl

/-- The proposition of `cleanup_keeps`. -/
def CleanupKeeps : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    (observe (Scenario.play (opened b) moves)).cleanupKeeps = true

/-- **Cleanup keeps the committed count.** Under every script the observation satisfies
`Observation.cleanupKeeps`. Each attempt that ended stands once in the cleanup log, with the
count its finalizer saw: its own number. So an interruption by the timer takes no committed
count back. Reach: the program `fetch`, every script of the driver's alphabet, the battery's
budgets. It is a statement about the log and the count cell: it counts writes by identity. It
does not count a finalizer's invocations, and it does not establish that a finalizer runs. It
states no cut inside a masked region: the attempt has none. Concept
`scope-lifetime-finalization`, R11. Consumer: the timeout scenario. Its controls are finite
runs, and the seat's receipt records a bounded search. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal cleanup_keeps : CleanupKeeps

/-- **The timeout scenario's claim.** Only the declared failures retry. A reply of a timed-out
attempt never applies to a later attempt. Cleanup keeps the committed count. The retry and cleanup clauses remain
planned goals, so this theorem is proved modulo them. It does not establish a Cache contract,
deadline fairness or a physical clock. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem timeout : RetriesDeclared ∧ StaleNeverApplies ∧ CleanupKeeps :=
  ⟨retries_declared, stale_never_applies, cleanup_keeps⟩

/-! ## 5. The runs and the controls -/

/-- A `[count seen, interrupted]` entry of the cleanup log. -/
def ended (attempt : Nat) (interrupted : Bool) : Val := .list [.nat attempt, .bool interrupted]

/-- The first attempt parked, with its call held: one attempt counted, nothing else. -/
def atParked : Observation :=
  { calls := [.live], receipts := [], applications := [], retired := [], stored := []
    attempts := 1, cleanups := [], root := .running, timers := [(2, 2000)] }

/-- The timer won the first attempt, and the second attempt is parked with its call held. -/
def atTimedOut : Observation :=
  { atParked with
    calls := [.retired false, .live]
    retired := [(key1, false)]
    attempts := 2
    cleanups := [ended 1 true]
    timers := [(4, 4100)] }

/-- The second attempt's reply was applied, and the root answered it. -/
def atSecond : Observation :=
  { atTimedOut with
    calls := [.retired false, .answered body2]
    receipts := [key2]
    applications := [key2]
    cleanups := [ended 1 true, ended 2 false]
    root := .answered body2
    timers := [] }

/-- Whether the original observation columns match.
The declared controls separately read completed timeout outcomes through `retriesDeclared`. -/
def shows (s : Run) (expected : Observation) : Bool :=
  { observe s with forms := [] } == { expected with forms := [] }

/-- The scenario's named runs: each script of a control, once, from one build of each program.
The first fourteen are on the fetch. The last two are on the client that retries every failure
and on the client whose finalizer resets the count. The host lane performs them in this order.
The first run, `parked`, is the part that every other script starts with. -/
def runsOf (b eager resetting : Api.Built) : List NamedRun :=
  let run := fun (name : String) (parts : List (List Move)) =>
    (⟨name, opened b, script parts⟩ : NamedRun)
  let notFound := [parked, answer http (failed "HttpError" "404"), [.tick 100, .flush, .hold http]]
  [ run "parked" [parked]
  , run "503" [parked, answer http (failed "HttpError" "503"), [.tick 100, .hold http],
      answer http (ok body2)]
  , run "timed-out" [timedOut]
  , run "four" [[.start, .tick 2000, .tick 100, .tick 2000, .tick 200, .tick 2000, .tick 400,
      .tick 2000]]
  , run "404" notFound
  , run "before" [parked, answer http (ok body1)]
  , run "second" [timedOut, answer second (ok body2)]
  , run "late" [timedOut, answer first (ok body1)]
  , run "kept" [parked, [.receive http (ok body1), .tick 2000, .apply first]]
  , run "crossed" [timedOut, [.wire (.submit (forged 0 key2 (ok body1)))]]
  , run "direct" [timedOut, [.control (.answerAsync ⟨3⟩ 6 (ok body1))]]
  , run "timer-interrupt" [parked, [.tick 2000]]
  , run "host-interrupt" [parked, [.cancel ⟨1⟩, .flush, .tick 2000, .tick 100]]
  , run "received" [parked, [.receive http (ok body1)]]
  , ⟨"eager", opened eager, script notFound⟩
  , ⟨"resetting", opened resetting, script [parked, [.tick 2000]]⟩ ]

/-- The controls. Each names the runs of `runsOf` that its comparison reads, and the gate hands
them over as played. Every control compares `observe`. A control of a refusal compares the
refused rows beside it. Two comparisons need the fetch's build: they play a journal again from
the opened program. The frontier control's comparison sets the fuel of a played run to zero and
plays one reply application: a script holds no budget, so that one move stays in the
comparison. -/
def controlsOf (b : Api.Built) : List Control :=
  [ -- only the declared failures retry
    green "declared" "a 503 is declared: after the delay the second attempt calls, and its reply answers"
      ["503"] fun
      | [retried] =>
        shows retried
          { atSecond with
            calls := [.failed "HttpError" "503", .answered body2]
            receipts := [key1, key2]
            applications := [key1, key2]
            retired := []
            cleanups := [ended 1 false, ended 2 false] } &&
          (observe retried).retriesDeclared
      | _ => false
  , green "declared" "a timeout is declared: the second attempt calls under its own key"
      ["timed-out"] fun
      | [retrying] =>
        shows retrying atTimedOut && (observe retrying).retriesDeclared &&
          (observe retrying).forms ==
            [⟨1, some ⟨2⟩, .timer, .failure (Cause.fail (.tagged "Timeout" "2000 ms"))⟩]
      | _ => false
  , green "declared" "four timeouts end the retries: the root fails with the timeout"
      ["four"] fun
      | [exhausted] =>
        shows exhausted
          { atParked with
            calls := []
            attempts := 4
            cleanups := [ended 1 true, ended 2 true, ended 3 true, ended 4 true]
            root := .failed "Timeout" "2000 ms"
            timers := [] } &&
          (observe exhausted).retriesDeclared &&
          (observe exhausted).forms.length == 4 &&
          (observe exhausted).forms.all (fun result => result.role == .timer)
      | _ => false
  , red "declared" "a 404 is not declared: the root fails with it, and no second attempt comes"
      ["404"] fun
      | [notFound] =>
        shows notFound
          { atParked with
            calls := [.failed "HttpError" "404"]
            receipts := [key1]
            applications := [key1]
            cleanups := [ended 1 false]
            root := .failed "HttpError" "404"
            timers := [] }
      | _ => false
  , red "declared" "a client that retries every failure calls again after the 404"
      ["eager"] fun
      | [eager] =>
        !(observe eager).retriesDeclared &&
          (observe eager).calls == [.failed "HttpError" "404", .live]
      | _ => false
    -- a reply of a timed-out attempt never applies to a later attempt
  , green "stale" "a reply before the timeout is applied, and the root answers it"
      ["before"] fun
      | [early] =>
        shows early
          { atParked with
            calls := [.answered body1]
            receipts := [key1]
            applications := [key1]
            cleanups := [ended 1 false]
            root := .answered body1
            timers := [] } &&
          (observe early).forms == [⟨1, some ⟨1⟩, .attempt, .success body1⟩]
      | _ => false
  , green "stale" "the second attempt's reply at its own key answers the root" ["second"] fun
      | [recorded] => shows recorded atSecond && (observe recorded).staleNeverApplies
      | _ => false
  , red "stale" "a reply after the timeout is refused twice, and the second attempt still waits"
      ["late"] fun
      | [late] => refused late [("submit", .noCall), ("apply", .noCall)] && shows late atTimedOut
      | _ => false
  , red "stale" "received before the timeout and applied after it: the reply is kept, never applied"
      ["kept"] fun
      | [kept] =>
        refused kept [("apply", .noCall)] &&
          shows kept
            { atParked with
              calls := [.retired true]
              receipts := [key1]
              retired := [(key1, true)]
              cleanups := [ended 1 true]
              timers := [(0, 2100)] }
      | _ => false
  , red "stale" "the first attempt's reply under the second attempt's key is refused"
      ["crossed"] fun
      | [crossed] => refused crossed [("submit", .callOrder)] && shows crossed atTimedOut
      | _ => false
    -- cleanup keeps the committed count
  , green "cleanup" "the first attempt counts itself before its call, and no finalizer ran"
      ["parked"] fun
      | [waiting] => shows waiting atParked && (observe waiting).cleanupKeeps
      | _ => false
  , green "cleanup" "the timer interrupts the first attempt: it is cleaned once, and its count stays"
      ["timer-interrupt"] fun
      | [interrupted] =>
        shows interrupted
          { atParked with
            calls := [.retired false]
            retired := [(key1, false)]
            cleanups := [ended 1 true]
            timers := [(0, 2100)] }
      | _ => false
  , green "cleanup" "the host interrupts the first attempt: it is cleaned once, and no attempt follows"
      ["host-interrupt"] fun
      | [cancelled] =>
        shows cancelled
          { atParked with
            calls := [.retired false]
            retired := [(key1, false)]
            cleanups := [ended 1 true]
            root := .interrupted
            timers := [] }
      | _ => false
  , red "cleanup" "a finalizer that resets the count loses the committed attempt"
      ["resetting"] fun
      | [resetting] => !(observe resetting).cleanupKeeps && (observe resetting).attempts == 0
      | _ => false
    -- an application at budget zero stops at a frontier
  , green "frontier" "at budget zero the reply application stops at a frontier, and the reply stays stored"
      ["received"] fun
      | [received] =>
        let starved : Run := { received with budget := { budget with fuel := 0 } }
        let stopped := Scenario.play starved [.apply http]
        stopped.phases.getLast? == some .frontier &&
          shows stopped { atParked with receipts := [key1], stored := [key1] }
      | _ => false
  , red "frontier" "with its budget the same row applies the reply and stores none"
      ["before"] fun
      | [applied] =>
        applied.phases.getLast? == some .applied && (observe applied).stored == []
      | _ => false
    -- the session refuses a direct answer decision
  , green "direct" "a reply receipt and a reply application move the run" ["second"] fun
      | [recorded] => shows recorded atSecond
      | _ => false
  , red "direct" "an answer decision at the second attempt's key is refused, and nothing moves"
      ["direct"] fun
      | [direct] => refused direct [("control", .directAnswer)] && shows direct atTimedOut
      | _ => false
    -- a script's run replays from its journal
  , green "journal" "the journal alone reaches the timed-out run again, verdict for verdict"
      ["second"] fun
      | [recorded] =>
        shows ((opened b).play recorded.journal) (observe recorded) &&
          ((opened b).play recorded.journal).phases == recorded.phases
      | _ => false
  , red "journal" "a journal that drops the timeout's clock row reaches another run"
      ["second"] fun
      | [recorded] => !shows ((opened b).play (recorded.journal.eraseIdx 3)) (observe recorded)
      | _ => false ]

/-- The scenario's runs and its controls, from one build of each program. A program that does
not build leaves no run and one failing control. -/
def runsAndControls : List NamedRun × List Control :=
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  match build fetch, build (client (fun _ => bool true) false), build (client retryable true) with
  | some b, some eager, some resetting => (runsOf b eager resetting, controlsOf b)
  | _, _, _ => ([], [green "declared" "the client and its variants build" [] fun _ => false])

/-! ## 6. The record -/

/-- The timeout scenario. The claim assembles the three clauses. The three laws are associated
laws: the record claims no dependency of `timeout` on them. -/
def scenario : Scenario :=
  { name := "timeout"
    program := ``fetch
    observation := ``observe
    claim := ``timeout
    clauses :=
      [ ⟨"declared", ``retries_declared⟩
      , ⟨"stale", ``stale_never_applies⟩
      , ⟨"cleanup", ``cleanup_keeps⟩ ]
    laws :=
      [ ⟨"frontier", ``Effect4.Api.HostSession.applyReply_zero⟩
      , ⟨"direct", ``Effect4.Api.HostSession.advance_answer_refuses⟩
      , ⟨"journal", ``replays⟩ ]
    runs := runsAndControls.1
    controls := runsAndControls.2 }

#scenario_gate scenario

end Test.Dogfood.Scenario.Timeout
