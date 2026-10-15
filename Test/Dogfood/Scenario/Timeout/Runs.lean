import Test.Dogfood.Scenario.Timeout.Model

/-! Data shared by the scenario battery and fixture writers. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Timeout

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario
open Test.Dogfood.P1HttpCache (getQuote timeoutForm retryForm retryable)

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


/-- The programs of this scenario, each admitted once. -/
def builtInputs : Option (Api.Built × Api.Built × Api.Built) := do
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  let b ← build fetch
  let eager ← build (client (fun _ => bool true) false)
  let resetting ← build (client retryable true)
  pure (b, eager, resetting)

/-- One inventory of the named scripts, read by every lane. -/
def runSet : RunSet :=
  { name := "timeout"
    runs := match builtInputs with
      | some (b, eager, resetting) => runsOf b eager resetting
      | none => [] }

end Test.Dogfood.Scenario.Timeout
