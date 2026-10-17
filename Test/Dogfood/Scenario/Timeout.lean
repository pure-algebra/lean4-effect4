import Test.Dogfood.Scenario.Timeout.Runs
import Test.Dogfood.Scenario.Timeout.Model

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Timeout

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario
open Test.Dogfood.P1HttpCache (getQuote timeoutForm retryForm retryable)

/-! ## 1. The runs and the controls -/

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
  match builtInputs with
  | some (b, _eager, _resetting) => (runSet.runs, controlsOf b)
  | none => ([], [green "declared" "the client and its variants build" [] fun _ => false])

/-! ## 2. The record -/

/-- The timeout scenario. The claim assembles the three clauses. The three laws are associated
laws: the record claims no dependency of `timeout` on them. -/
def scenario : Scenario :=
  { name := runSet.name
    program := ``fetch
    observation := ``observe
    runs := runsAndControls.1
    controls := runsAndControls.2 }

end Test.Dogfood.Scenario.Timeout

