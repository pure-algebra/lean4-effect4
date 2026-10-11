import Test.Dogfood.Scenario.Timeout

open Effect4 Effect4.Machine Test.Dogfood.Scenario.Timeout

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The counterexample's script. -/
def cx : List Test.Dogfood.Scenario.Move :=
  Test.Dogfood.Scenario.script [parked, [.cancel ⟨3⟩, .receive http (Test.Dogfood.Scenario.ok body1),
    .apply http, .tick 2000, .tick 100, .flush, .hold http]]

-- the build alone, by the kernel
set_option trace.profiler true in
theorem build_isOk : (Effect4.Api.Author.build fetch).toOption.isSome = true := by decide +kernel

-- the counterexample's run, by the kernel
set_option trace.profiler true in
theorem cx_refutes : (Effect4.Api.Author.build fetch).toOption.map
    (fun b => (observe (Test.Dogfood.Scenario.play (opened b) cx)).retriesDeclared) = some false := by
  decide +kernel
