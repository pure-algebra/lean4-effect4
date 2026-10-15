import Test.Dogfood.Scenario.Atomic.Model

/-! Data shared by the scenario battery and fixture writers. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Atomic

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P4RateLimiter (window0 windowTy windowVal decision refill)
open Test.Dogfood.P5LedgerService (account0 deposited)

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


/-- The programs of this scenario, each admitted once. -/
def builtInputs : Option (Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built) := do
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  let b ← build (shop .none)
  let racy ← build (shop .racy)
  let erased ← build (shop .erased)
  let undone ← build (shop .undone)
  let twice ← build (shop .twice)
  let suspended ← build (alone .none true)
  let plain ← build (alone .none false)
  let aloneUndone ← build (alone .undone false)
  pure (b, racy, erased, undone, twice, suspended, plain, aloneUndone)

/-- One inventory of the named scripts, read by every lane. -/
def runSet : RunSet :=
  { name := "atomic"
    runs := match builtInputs with
      | some (b, racy, erased, undone, twice, _suspended, _plain, _aloneUndone) => runsOf b racy erased undone twice
      | none => [] }

end Test.Dogfood.Scenario.Atomic
